import Solcore.SourceSemantics.Dynamic.Fault
/-! Sizes of the existing finite source derivations. Each rule contributes
one plus the sum of all its immediate dynamic premises. The fault group counts
successful prefixes as well as faulting children. Static dispatch, evidence,
shape and allocation facts are retained unchanged. Erasure and existence relate
these witnesses to the original judgments; no execution procedure is added. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.SourceExecutionSize
open Frontend Frontend.SourceInference TypeSystem Solcore.SourceSemantics.Dynamic

def stepSize (children : List Nat) : Nat := children.sum + 1

theorem stepSize_positive (children : List Nat) : 0 < stepSize children := by
  simp [stepSize]

theorem child_lt_stepSize {child : Nat} {children : List Nat}
    (member : child ∈ children) : child < stepSize children := by
  have bound : child ≤ children.sum := by
    induction children with
    | nil => cases member
    | cons head rest ih =>
      rcases List.mem_cons.mp member with rfl | member
      · simp
      · have bound := ih member
        simp only [List.sum_cons]
        omega
  unfold stepSize
  omega

mutual
  inductive ExpressionEvaluates (program : Program) : Nat →
      Context → EvidenceEnvironment → TypedSource → Dynamic.Environment →
        Heap → ExpressionId → Value → Heap → Prop where
    | intro
        {size_form size_coercions : Nat}
        {context : Context}
        {evidence : EvidenceEnvironment}
        {source : TypedSource}
        {environment : Dynamic.Environment}
        {before middle after : Heap}
        {id : ExpressionId}
        {node : ExpressionNode}
        {raw result : Value}
        (contains : ContainsExpression source id node)
        (form : ExpressionFormEvaluates program size_form context evidence source
          environment before node.form node.requirements node.coercions raw middle)
        (coercions : CoercionPathExecutes program size_coercions context evidence middle
          node.coercions raw result after) :
        ExpressionEvaluates program (stepSize [size_form, size_coercions]) context evidence source environment before
          id result after
    | generalizedLocal
        {size_coercions : Nat}
        {context : Context}
        {evidence : EvidenceEnvironment}
        {source : TypedSource}
        {environment : Dynamic.Environment}
        {before after : Heap}
        {id : ExpressionId}
        {node : ExpressionNode}
        {name : String}
        {binder : Resolved.LocalId}
        {owned : List RequirementId}
        {location : Location}
        {cell : Cell}
        {function : GeneralizedClosure}
        {substitution : Substitution}
        {produced : EvidenceEnvironment}
        {value : Value}
        (contains : ContainsExpression source id node)
        (form_eq : node.form = .reference name (.local binder))
        (layout : OrdinaryRequirementLayout node.requirements node.coercions
          owned)
        (lookup : Dynamic.Environment.LooksUp environment binder location)
        (read : Heap.Reads before location cell)
        (descriptor : cell.generalized = some function)
        (context_fields : RuntimeContextFields function.definitionContext
          context)
        (instantiation : LocalSchemeRuntimeInstantiation context evidence
          function.binder node.rawType owned substitution produced)
        (coercions : CoercionPathExecutes program size_coercions context evidence before
          node.coercions
          (.closure (function.instantiate substitution
            (produced ++ evidence.applySubstitution substitution)))
          value after) :
        ExpressionEvaluates program (stepSize [size_coercions]) context evidence source environment before
          id value after

  inductive ExpressionFormEvaluates (program : Program) : Nat →
      Context → EvidenceEnvironment → TypedSource → Dynamic.Environment →
        Heap → ExpressionForm → List RequirementId →
        List CoercionStep → Value → Heap → Prop where
    | literal
        {context evidence source environment heap literal requirements coercions
          value}
        (layout : OrdinaryRequirementLayout requirements coercions [])
        (constructs : LiteralConstructs literal value) :
        ExpressionFormEvaluates program (stepSize []) context evidence source environment heap
          (.literal literal) requirements coercions value heap
    | integerLiteral
        {context evidence source environment heap literal resolution requirements
          coercions value}
        (layout : OrdinaryRequirementLayout requirements coercions
          [resolution.requirement])
        (constructs : ResolvedIntegerLiteralConstructs context literal resolution
          value) :
        ExpressionFormEvaluates program (stepSize []) context evidence source environment heap
          (.integerLiteral literal resolution) requirements coercions value heap
    | local
        {context evidence source environment heap name binder requirements coercions
          location cell value}
        (layout : OrdinaryRequirementLayout requirements coercions [])
        (lookup : Dynamic.Environment.LooksUp environment binder location)
        (read : Heap.Reads heap location cell)
        (descriptor_empty : cell.generalized = none)
        (initialized : cell.value = some value) :
        ExpressionFormEvaluates program (stepSize []) context evidence source environment heap
          (.reference name (.local binder)) requirements coercions value heap
    | localEmptyMapping
        {context evidence source environment before after name binder requirements
          coercions location cell keyType valueType}
        (layout : OrdinaryRequirementLayout requirements coercions [])
        (lookup : Dynamic.Environment.LooksUp environment binder location)
        (read : Heap.Reads before location cell)
        (descriptor_empty : cell.generalized = none)
        (type_eq : cell.type = .mapping keyType valueType)
        (empty : cell.value = none)
        (write : Heap.Writes before location
          (some (.mapping keyType valueType [])) after) :
        ExpressionFormEvaluates program (stepSize []) context evidence source environment before
          (.reference name (.local binder)) requirements coercions
          (.mapping keyType valueType []) after
    | declaration
        {context evidence source environment heap name instantiation requirements
          coercions owned produced}
        (layout : OrdinaryRequirementLayout requirements coercions owned)
        (valid : SourceSemantics.DeclarationInstantiation.Valid
          context instantiation)
        (requirements_close : RequirementsProduceEnvironment context evidence owned
          instantiation.predicates produced) :
        ExpressionFormEvaluates program (stepSize []) context evidence source environment heap
          (.reference name (.declaration instantiation)) requirements coercions
          (.global ⟨instantiation, produced⟩) heap
    | builtinFunction
        {context evidence source environment heap name function requirements
          coercions}
        (layout : OrdinaryRequirementLayout requirements coercions []) :
        ExpressionFormEvaluates program (stepSize []) context evidence source environment heap
          (.reference name (.builtinFunction function)) requirements coercions
          (.builtin ⟨function⟩) heap
    | builtinBoolean
        {context evidence source environment heap name value requirements coercions}
        (layout : OrdinaryRequirementLayout requirements coercions []) :
        ExpressionFormEvaluates program (stepSize []) context evidence source environment heap
          (.reference name (.builtinBoolean value)) requirements coercions
          (.bool value) heap
    | group
        {size_inner_evaluates : Nat}
        {context evidence source environment before after inner requirements
          coercions value}
        (layout : OrdinaryRequirementLayout requirements coercions [])
        (inner_evaluates : ExpressionEvaluates program size_inner_evaluates context evidence source
          environment before inner value after) :
        ExpressionFormEvaluates program (stepSize [size_inner_evaluates]) context evidence source environment before
          (.group inner) requirements coercions value after
    | tuple
        {size_elements_evaluate : Nat}
        {context evidence source environment before after elements requirements
          coercions values packed}
        (layout : OrdinaryRequirementLayout requirements coercions [])
        (elements_evaluate : ExpressionsEvaluate program size_elements_evaluate context evidence source
          environment before elements values after)
        (pack : ValuesPack values packed) :
        ExpressionFormEvaluates program (stepSize [size_elements_evaluate]) context evidence source environment before
          (.tuple elements) requirements coercions packed after
    | unary
        {size_operand_evaluates size_applies : Nat}
        {context evidence source environment before middle after operator operand
          requirements coercions owned input output}
        (layout : OrdinaryRequirementLayout requirements coercions owned)
        (operand_evaluates : ExpressionEvaluates program size_operand_evaluates context evidence source
          environment before operand input middle)
        (applies : UnaryOperationApplies program size_applies context evidence middle operator
          owned input output after) :
        ExpressionFormEvaluates program (stepSize [size_operand_evaluates, size_applies]) context evidence source environment before
          (.unary operator operand) requirements coercions output after
    | binaryShortCircuit
        {size_left_evaluates : Nat}
        {context evidence source environment before after left operator right
          requirements coercions owned leftValue result}
        (layout : OrdinaryRequirementLayout requirements coercions owned)
        (left_evaluates : ExpressionEvaluates program size_left_evaluates context evidence source
          environment before left leftValue after)
        (circuit : ShortCircuits operator leftValue result)
        (owned_empty : owned = []) :
        ExpressionFormEvaluates program (stepSize [size_left_evaluates]) context evidence source environment before
          (.binary left operator right) requirements coercions result after
    | binaryEvaluateRight
        {size_left_evaluates size_right_evaluates size_applies : Nat}
        {context evidence source environment before leftHeap rightHeap after
          left operator right requirements coercions owned leftValue rightValue
          result}
        (layout : OrdinaryRequirementLayout requirements coercions owned)
        (left_evaluates : ExpressionEvaluates program size_left_evaluates context evidence source
          environment before left leftValue leftHeap)
        (evaluate_right : EvaluatesRightOperand operator leftValue)
        (right_evaluates : ExpressionEvaluates program size_right_evaluates context evidence source
          environment leftHeap right rightValue rightHeap)
        (applies : BinaryOperationApplies program size_applies context evidence rightHeap
          operator owned leftValue rightValue result after) :
        ExpressionFormEvaluates program (stepSize [size_left_evaluates, size_right_evaluates, size_applies]) context evidence source environment before
          (.binary left operator right) requirements coercions result after
    | conditionalTrue
        {size_condition_evaluates size_branch_evaluates : Nat}
        {context evidence source environment before middle after condition
          thenBranch elseBranch requirements coercions value}
        (layout : OrdinaryRequirementLayout requirements coercions [])
        (condition_evaluates : ExpressionEvaluates program size_condition_evaluates context evidence source
          environment before condition (.bool true) middle)
        (branch_evaluates : ExpressionEvaluates program size_branch_evaluates context evidence source
          environment middle thenBranch value after) :
        ExpressionFormEvaluates program (stepSize [size_condition_evaluates, size_branch_evaluates]) context evidence source environment before
          (.conditional condition thenBranch elseBranch) requirements coercions
          value after
    | conditionalFalse
        {size_condition_evaluates size_branch_evaluates : Nat}
        {context evidence source environment before middle after condition
          thenBranch elseBranch requirements coercions value}
        (layout : OrdinaryRequirementLayout requirements coercions [])
        (condition_evaluates : ExpressionEvaluates program size_condition_evaluates context evidence source
          environment before condition (.bool false) middle)
        (branch_evaluates : ExpressionEvaluates program size_branch_evaluates context evidence source
          environment middle elseBranch value after) :
        ExpressionFormEvaluates program (stepSize [size_condition_evaluates, size_branch_evaluates]) context evidence source environment before
          (.conditional condition thenBranch elseBranch) requirements coercions
          value after
    | lambda
        {context evidence source environment heap parameters returnType body
          requirements coercions}
        (layout : OrdinaryRequirementLayout requirements coercions []) :
        ExpressionFormEvaluates program (stepSize []) context evidence source environment heap
          (.lambda parameters returnType body) requirements coercions
          (.closure {
            parameters := parameters
            resultType := returnType
            body := body
            source := source
            captured := environment
            context := context
            evidence := evidence
          }) heap
    | directCall
        {size_arguments_evaluate size_applies : Nat}
        {context evidence source environment before argumentsHeap after
          callee arguments instantiation requirements coercions argumentValues
          calleeEvidence result calleeNode name}
        (callee_contains : ContainsExpression source callee calleeNode)
        (callee_form : calleeNode.form =
          .reference name (.declaration instantiation))
        (callee_requirements : calleeNode.requirements = [])
        (callee_coercions : calleeNode.coercions = [])
        (valid : SourceSemantics.DeclarationInstantiation.Valid
          context instantiation)
        (arguments_evaluate : ExpressionsEvaluate program size_arguments_evaluate context evidence source
          environment before arguments argumentValues argumentsHeap)
        (call_evidence : DirectCallProducesEvidence context evidence requirements
          coercions instantiation.predicates calleeEvidence)
        (applies : CallableApplies program size_applies context evidence calleeEvidence
          argumentsHeap (.global ⟨instantiation, calleeEvidence⟩)
          argumentValues result after) :
        ExpressionFormEvaluates program (stepSize [size_arguments_evaluate, size_applies]) context evidence source environment before
          (.call callee arguments (.declaration instantiation)) requirements
          coercions result after
    | builtinCall
        {size_arguments_evaluate size_applies : Nat}
        {context evidence source environment before argumentsHeap after
          callee arguments function requirements coercions argumentValues result}
        (layout : OrdinaryRequirementLayout requirements coercions [])
        (arguments_evaluate : ExpressionsEvaluate program size_arguments_evaluate context evidence source
          environment before arguments argumentValues argumentsHeap)
        (applies : CallableApplies program size_applies context evidence [] argumentsHeap
          (.builtin ⟨function⟩) argumentValues result after) :
        ExpressionFormEvaluates program (stepSize [size_arguments_evaluate, size_applies]) context evidence source environment before
          (.call callee arguments (.builtinFunction function)) requirements
          coercions result after
    | indirectCall
        {size_callee_evaluates size_arguments_evaluate size_argument_coercions size_applies : Nat}
        {context evidence source environment before calleeHeap argumentHeap
          coercedHeap after callee arguments metadata requirements coercions
          callable argumentValues packed coerced appliedArguments result
          invocationEvidence}
        (requirements_eq : requirements =
          coercionRequirementIds metadata.argumentCoercions ++
            coercionRequirementIds coercions)
        (callee_evaluates : ExpressionEvaluates program size_callee_evaluates context evidence source
          environment before callee callable calleeHeap)
        (arguments_evaluate : ExpressionsEvaluate program size_arguments_evaluate context evidence source
          environment calleeHeap arguments argumentValues argumentHeap)
        (pack_before : ValuesPack argumentValues packed)
        (argument_coercions : CoercionPathExecutes program size_argument_coercions context evidence
          argumentHeap metadata.argumentCoercions packed coerced coercedHeap)
        (pack_after : ValuesPack appliedArguments coerced)
        (source_arity : arguments.length = metadata.argumentCount)
        (applied_arity : appliedArguments.length = metadata.argumentCount)
        (applies : CallableApplies program size_applies context evidence invocationEvidence coercedHeap
          callable appliedArguments result after) :
        ExpressionFormEvaluates program (stepSize [size_callee_evaluates, size_arguments_evaluate, size_argument_coercions, size_applies]) context evidence source environment before
          (.call callee arguments (.indirect metadata)) requirements coercions
          result after
    | constructor
        {size_arguments_evaluate : Nat}
        {context evidence source environment before after instantiation arguments
          requirements coercions values}
        (layout : OrdinaryRequirementLayout requirements coercions [])
        (valid : DataConstructorInstantiation.Valid context instantiation)
        (arguments_evaluate : ExpressionsEvaluate program size_arguments_evaluate context evidence source
          environment before arguments values after) :
        ExpressionFormEvaluates program (stepSize [size_arguments_evaluate]) context evidence source environment before
          (.constructor instantiation arguments) requirements coercions
          (.constructed instantiation values) after
    | member
        {size_base_evaluates : Nat}
        {context evidence source environment before after base name index
          requirements coercions instantiation arguments selected}
        (layout : OrdinaryRequirementLayout requirements coercions [])
        (base_evaluates : ExpressionEvaluates program size_base_evaluates context evidence source
          environment before base (.constructed instantiation arguments) after)
        (selected_at : ValueAt arguments index selected) :
        ExpressionFormEvaluates program (stepSize [size_base_evaluates]) context evidence source environment before
          (.member base name index) requirements coercions selected after
    | proxy
        {context evidence source environment heap inner requirements coercions}
        (layout : OrdinaryRequirementLayout requirements coercions []) :
        ExpressionFormEvaluates program (stepSize []) context evidence source environment heap
          (.proxy inner) requirements coercions (.proxy inner) heap
    | indexFound
        {size_base_evaluates size_index_evaluates : Nat}
        {context evidence source environment before middle after base index
          requirements coercions keyType valueType entries key value}
        (layout : OrdinaryRequirementLayout requirements coercions [])
        (base_evaluates : ExpressionEvaluates program size_base_evaluates context evidence source
          environment before base (.mapping keyType valueType entries) middle)
        (index_evaluates : ExpressionEvaluates program size_index_evaluates context evidence source
          environment middle index key after)
        (lookup : MappingLookup key entries value) :
        ExpressionFormEvaluates program (stepSize [size_base_evaluates, size_index_evaluates]) context evidence source environment before
          (.index base index) requirements coercions value after
    | indexDefault
        {size_base_evaluates size_index_evaluates : Nat}
        {context evidence source environment before middle after base index
          requirements coercions keyType valueType entries key value}
        (layout : OrdinaryRequirementLayout requirements coercions [])
        (base_evaluates : ExpressionEvaluates program size_base_evaluates context evidence source
          environment before base (.mapping keyType valueType entries) middle)
        (index_evaluates : ExpressionEvaluates program size_index_evaluates context evidence source
          environment middle index key after)
        (absent : MappingAbsent key entries)
        (defaulted : DefaultValue valueType value) :
        ExpressionFormEvaluates program (stepSize [size_base_evaluates, size_index_evaluates]) context evidence source environment before
          (.index base index) requirements coercions value after

  inductive ExpressionsEvaluate (program : Program) : Nat →
      Context → EvidenceEnvironment → TypedSource → Dynamic.Environment →
        Heap → List ExpressionId → List Value → Heap → Prop where
    | nil
        {context evidence source environment heap} :
        ExpressionsEvaluate program (stepSize []) context evidence source environment heap [] []
          heap
    | cons
        {size_head size_tail : Nat}
        {context evidence source environment before middle after expression
          expressions value values}
        (head : ExpressionEvaluates program size_head context evidence source environment
          before expression value middle)
        (tail : ExpressionsEvaluate program size_tail context evidence source environment
          middle expressions values after) :
        ExpressionsEvaluate program (stepSize [size_head, size_tail]) context evidence source environment before
          (expression :: expressions) (value :: values) after

  inductive SourceProjectionsEvaluate (program : Program) : Nat →
      Context → EvidenceEnvironment → TypedSource → Dynamic.Environment → Heap →
        List PlaceProjection → List EvaluatedProjection → Heap → Prop where
    | nil
        {context evidence source environment heap} :
        SourceProjectionsEvaluate program (stepSize []) context evidence source environment heap
          [] [] heap
    | member
        {size_tail : Nat}
        {context evidence source environment before after name index projections
          evaluated}
        (tail : SourceProjectionsEvaluate program size_tail context evidence source environment
          before projections evaluated after) :
        SourceProjectionsEvaluate program (stepSize [size_tail]) context evidence source environment before
          (.member name index :: projections)
          (.member name index :: evaluated) after
    | index
        {size_head size_tail : Nat}
        {context evidence source environment before middle after expression key
          projections evaluated}
        (head : ExpressionEvaluates program size_head context evidence source environment
          before expression key middle)
        (tail : SourceProjectionsEvaluate program size_tail context evidence source environment
          middle projections evaluated after) :
        SourceProjectionsEvaluate program (stepSize [size_head, size_tail]) context evidence source environment before
          (.index expression :: projections) (.index key :: evaluated) after

  inductive SourcePlaceResolves (program : Program) : Nat →
      Context → EvidenceEnvironment → TypedSource → Dynamic.Environment → Heap →
        PlaceResolution → ResolvedPlace → Heap → Prop where
    | intro
        {size_evaluate : Nat}
        {context evidence source environment before after place location initialCell
          currentCell evaluated initial selected}
        (root_lookup : Dynamic.Environment.LooksUp environment place.root location)
        (initial_read : Heap.Reads before location initialCell)
        (evaluate : SourceProjectionsEvaluate program size_evaluate context evidence source
          environment before place.projections evaluated after)
        (current_read : Heap.Reads after location currentCell)
        (initial_value : RootInitialValue currentCell initial)
        (selection : ProjectionsRead initial evaluated selected) :
        SourcePlaceResolves program (stepSize [size_evaluate]) context evidence source environment before place
          { location := location
            rootType := currentCell.type
            valueType := place.type
            projections := evaluated
            selected := selected }
          after

  inductive SourcePlaceAssignment (program : Program) : Nat →
      Context → EvidenceEnvironment → TypedSource →
        (Option Value → Value → Value → Prop) →
        Dynamic.Environment → Heap → PlaceResolution → ExpressionId →
        Value → Heap → Prop where
    | intro
        {size_resolve size_evaluate_right : Nat}
        {context evidence source combine environment before targetHeap rhsHeap after
          place target rightExpression rightValue updatedRoot}
        (resolve : SourcePlaceResolves program size_resolve context evidence source environment
          before place target targetHeap)
        (evaluate_right : ExpressionEvaluates program size_evaluate_right context evidence source
          environment targetHeap rightExpression rightValue rhsHeap)
        (write : ResolvedPlaceWrites
          (fun _ updated => combine target.selected rightValue updated)
          rhsHeap target updatedRoot after) :
        SourcePlaceAssignment program (stepSize [size_resolve, size_evaluate_right]) context evidence source combine environment
          before place rightExpression updatedRoot after

  inductive SourcePlaceSnapshotUpdate (program : Program) : Nat →
      Context → EvidenceEnvironment → TypedSource →
        (Option Value → Value → Prop) → Dynamic.Environment → Heap →
        PlaceResolution → Value → Heap → Prop where
    | intro
        {size_resolve : Nat}
        {context evidence source modify environment before selectedHeap after place
          target updatedRoot}
        (resolve : SourcePlaceResolves program size_resolve context evidence source environment
          before place target selectedHeap)
        (write : ResolvedPlaceWrites
          (fun _ updated => modify target.selected updated)
          selectedHeap target updatedRoot after) :
        SourcePlaceSnapshotUpdate program (stepSize [size_resolve]) context evidence source modify environment
          before place updatedRoot after

  inductive UnaryOperationApplies (program : Program) : Nat →
      Context → EvidenceEnvironment → Heap → Syntax.UnaryOp →
        List RequirementId → Value → Value → Heap → Prop where
    | primitive
        {context evidence heap operator input output}
        (applies : UnaryPrimitiveApplies operator input output) :
        UnaryOperationApplies program (stepSize []) context evidence heap operator [] input
          output heap
    | method
        {size_invokes : Nat}
        {context evidence before after operator input output requirements
          traitName methodName bodyInstance calleeEvidence}
        (dispatch : UnaryTraitDispatch operator traitName methodName)
        (selected : OperatorMethodSelected program context evidence traitName
          methodName requirements bodyInstance calleeEvidence)
        (invokes : BodyInvokes program size_invokes bodyInstance calleeEvidence before [input]
          output after) :
        UnaryOperationApplies program (stepSize [size_invokes]) context evidence before operator requirements
          input output after

  inductive BinaryOperationApplies (program : Program) : Nat →
      Context → EvidenceEnvironment → Heap → Syntax.BinaryOp →
        List RequirementId → Value → Value → Value → Heap → Prop where
    | primitive
        {context evidence heap operator left right output}
        (applies : BinaryPrimitiveApplies operator left right output) :
        BinaryOperationApplies program (stepSize []) context evidence heap operator [] left right
          output heap
    | method
        {size_invokes : Nat}
        {context evidence before after operator left right output requirements
          traitName methodName bodyInstance calleeEvidence}
        (dispatch : BinaryTraitDispatch operator traitName methodName)
        (selected : OperatorMethodSelected program context evidence traitName
          methodName requirements bodyInstance calleeEvidence)
        (invokes : BodyInvokes program size_invokes bodyInstance calleeEvidence before
          [left, right] output after) :
        BinaryOperationApplies program (stepSize [size_invokes]) context evidence before operator requirements
          left right output after

  inductive CoercionStepExecutes (program : Program) : Nat →
      Context → EvidenceEnvironment → Heap → CoercionStep →
        Value → Value → Heap → Prop where
    | primitive
        {context evidence heap step input output}
        (no_source_method : ∀ bodyInstance calleeEvidence,
          ¬ OperatorMethodSelected program context evidence "Coerce" "coerce"
            step.requirements bodyInstance calleeEvidence)
        (applies : CoercionApplies context step input output) :
        CoercionStepExecutes program (stepSize []) context evidence heap step input output heap
    | method
        {size_invokes : Nat}
        {context evidence before after step input output bodyInstance calleeEvidence}
        (selected : OperatorMethodSelected program context evidence "Coerce"
          "coerce" step.requirements bodyInstance calleeEvidence)
        (invokes : BodyInvokes program size_invokes bodyInstance calleeEvidence before [input]
          output after) :
        CoercionStepExecutes program (stepSize [size_invokes]) context evidence before step input output after

  inductive CoercionPathExecutes (program : Program) : Nat →
      Context → EvidenceEnvironment → Heap → List CoercionStep →
        Value → Value → Heap → Prop where
    | nil
        {context evidence heap value} :
        CoercionPathExecutes program (stepSize []) context evidence heap [] value value heap
    | cons
        {size_head size_tail : Nat}
        {context evidence before middle after step steps input converted output}
        (head : CoercionStepExecutes program size_head context evidence before step input
          converted middle)
        (tail : CoercionPathExecutes program size_tail context evidence middle steps converted
          output after) :
        CoercionPathExecutes program (stepSize [size_head, size_tail]) context evidence before (step :: steps) input
          output after

  inductive CallableApplies (program : Program) : Nat →
      Context → EvidenceEnvironment → EvidenceEnvironment → Heap →
        Value → List Value → Value → Heap → Prop where
    | builtin
        {context callerEvidence invocationEvidence heap function arguments result}
        (applies : BuiltinApplies function.id arguments result) :
        CallableApplies program (stepSize []) context callerEvidence invocationEvidence heap
          (.builtin function) arguments result heap
    | global
        {size_invokes : Nat}
        {context callerEvidence invocationEvidence before after function arguments
          result bodyInstance}
        (instantiates : FunctionInstantiates program function.instantiation
          bodyInstance)
        (invocation_eq : invocationEvidence = function.evidence)
        (covers : invocationEvidence.Covers bodyInstance.context)
        (invokes : BodyInvokes program size_invokes bodyInstance invocationEvidence before
          arguments result after) :
        CallableApplies program (stepSize [size_invokes]) context callerEvidence invocationEvidence before
          (.global function) arguments result after
    | closure
        {size_execute : Nat}
        {context callerEvidence invocationEvidence before bound after function
          arguments environment outcome result parameterTypes callContext
          finalContext}
        (invocation_eq : invocationEvidence = function.evidence)
        (frame : ClosureFrame program function)
        (parameters_extend : MonoBindersExtend function.source.owner
          function.context function.parameters parameterTypes callContext)
        (allocate : BindersAllocate function.captured before function.parameters
          arguments environment bound)
        (execute : FunctionStatementsExecute program size_execute callContext function.evidence
          function.source environment bound function.body finalContext outcome after)
        (returned : outcome = .returned result) :
        CallableApplies program (stepSize [size_execute]) context callerEvidence invocationEvidence before
          (.closure function) arguments result after
    | closureUnit
        {size_execute : Nat}
        {context callerEvidence invocationEvidence before bound after function
          arguments environment outcome parameterTypes callContext finalContext}
        (invocation_eq : invocationEvidence = function.evidence)
        (frame : ClosureFrame program function)
        (result_unit : function.resultType = .unit)
        (parameters_extend : MonoBindersExtend function.source.owner
          function.context function.parameters parameterTypes callContext)
        (allocate : BindersAllocate function.captured before function.parameters
          arguments environment bound)
        (execute : FunctionStatementsExecute program size_execute callContext function.evidence
          function.source environment bound function.body finalContext outcome after)
        (fell_through : ∃ finalEnvironment,
          outcome = .fallthrough finalEnvironment) :
        CallableApplies program (stepSize [size_execute]) context callerEvidence invocationEvidence before
          (.closure function) arguments .unit after

  inductive BodyInvokes (program : Program) : Nat →
      BodyInstance → EvidenceEnvironment → Heap → List Value →
        Value → Heap → Prop where
    | returned
        {size_execute : Nat}
        {bodyInstance evidence before bound after arguments environment roots result
          outcome inputTypes lexicalContext finalContext}
        (covers : evidence.Covers bodyInstance.context)
        (roots_eq : StatementRoots bodyInstance.source.roots roots)
        (inputs_extend : MonoBindersExtend bodyInstance.source.owner
          bodyInstance.context bodyInstance.source.inputs inputTypes lexicalContext)
        (allocate : BindersAllocate [] before bodyInstance.source.inputs arguments
          environment bound)
        (execute : FunctionStatementsExecute program size_execute lexicalContext evidence
          bodyInstance.source environment bound roots finalContext outcome after)
        (returned : outcome = .returned result) :
        BodyInvokes program (stepSize [size_execute]) bodyInstance evidence before arguments result after
    | unit
        {size_execute : Nat}
        {bodyInstance evidence before bound after arguments environment roots
          outcome inputTypes lexicalContext finalContext}
        (covers : evidence.Covers bodyInstance.context)
        (result_unit : bodyInstance.resultType = .unit)
        (roots_eq : StatementRoots bodyInstance.source.roots roots)
        (inputs_extend : MonoBindersExtend bodyInstance.source.owner
          bodyInstance.context bodyInstance.source.inputs inputTypes lexicalContext)
        (allocate : BindersAllocate [] before bodyInstance.source.inputs arguments
          environment bound)
        (execute : FunctionStatementsExecute program size_execute lexicalContext evidence
          bodyInstance.source environment bound roots finalContext outcome after)
        (fell_through : ∃ finalEnvironment,
          outcome = .fallthrough finalEnvironment) :
        BodyInvokes program (stepSize [size_execute]) bodyInstance evidence before arguments .unit after

  inductive StatementExecutes (program : Program) : Nat →
      Context → EvidenceEnvironment → TypedSource → Dynamic.Environment →
        Heap → StatementId → Context → ControlOutcome → Heap → Prop where
    | letUninitialized
        {context finalContext evidence source environment before after id node binder
          location}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .letDecl binder none)
        (monomorphic : binder.scheme.quantified = [])
        (extension : BinderExtends source.owner context binder finalContext)
        (allocate : Heap.Allocates before binder.scheme.body none location after) :
        StatementExecutes program (stepSize []) context evidence source environment before id
          finalContext (.fallthrough ((binder.id, location) :: environment)) after
    | letInitialized
        {size_evaluate : Nat}
        {context finalContext evidence source environment before middle after id node
          binder initializer value location}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .letDecl binder (some initializer))
        (evaluate : ExpressionEvaluates program size_evaluate context evidence source environment
          before initializer value middle)
        (monomorphic : binder.scheme.quantified = [])
        (extension : BinderExtends source.owner context binder finalContext)
        (allocate : Heap.Allocates middle binder.scheme.body (some value) location
          after) :
        StatementExecutes program (stepSize [size_evaluate]) context evidence source environment before id
          finalContext (.fallthrough ((binder.id, location) :: environment)) after
    | letInitializedGeneralized
        {context finalContext evidence source environment before after id node binder
          initializer function location}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .letDecl binder (some initializer))
        (captures : GeneralizedClosureCaptures context source environment binder
          initializer function)
        (polymorphic : binder.scheme.quantified ≠ [])
        (extension : BinderExtends source.owner context binder finalContext)
        (allocate : Heap.AllocatesGeneralized before function location after) :
        StatementExecutes program (stepSize []) context evidence source environment before id
          finalContext (.fallthrough ((binder.id, location) :: environment)) after
    | returnUnit
        {context evidence source environment heap id node}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .returnStmt none) :
        StatementExecutes program (stepSize []) context evidence source environment heap id
          context (.returned .unit) heap
    | returnValue
        {size_evaluate : Nat}
        {context evidence source environment before after id node expression value}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .returnStmt (some expression))
        (evaluate : ExpressionEvaluates program size_evaluate context evidence source environment
          before expression value after) :
        StatementExecutes program (stepSize [size_evaluate]) context evidence source environment before id
          context (.returned value) after
    | expression
        {size_evaluate : Nat}
        {context evidence source environment before after id node expression
          semicolon value}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .expression expression semicolon)
        (evaluate : ExpressionEvaluates program size_evaluate context evidence source environment
          before expression value after) :
        StatementExecutes program (stepSize [size_evaluate]) context evidence source environment before id
          context (.fallthrough environment) after
    | assignValue
        {size_assignment_executes : Nat}
        {context evidence source environment before after id node assignment
          operator rhs updatedRoot}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .assignValue assignment operator rhs)
        (assignment_executes : SourcePlaceAssignment program size_assignment_executes context evidence source
          (AssignmentValueApplies operator) environment before assignment.target rhs
          updatedRoot after) :
        StatementExecutes program (stepSize [size_assignment_executes]) context evidence source environment before id
          context (.fallthrough environment) after
    | assignBitNot
        {size_assignment_executes : Nat}
        {context evidence source environment before after id node assignment
          updatedRoot}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .assignBitNot assignment)
        (assignment_executes : SourcePlaceSnapshotUpdate program size_assignment_executes context evidence
          source BitNotSnapshot environment before assignment.target updatedRoot
          after) :
        StatementExecutes program (stepSize [size_assignment_executes]) context evidence source environment before id
          context (.fallthrough environment) after
    | ifTrue
        {size_condition_evaluates size_body_executes : Nat}
        {context evidence source environment before middle after id node condition
          thenBody elseBody innerFinalContext outcome}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .ifThen condition thenBody elseBody)
        (condition_evaluates : ExpressionEvaluates program size_condition_evaluates context evidence source
          environment before condition (.bool true) middle)
        (body_executes : StatementsExecute program size_body_executes context evidence source
          environment middle thenBody innerFinalContext outcome after) :
        StatementExecutes program (stepSize [size_condition_evaluates, size_body_executes]) context evidence source environment before id
          context (restoreControl environment outcome) after
    | ifFalseWithoutElse
        {size_condition_evaluates : Nat}
        {context evidence source environment before after id node condition thenBody}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .ifThen condition thenBody none)
        (condition_evaluates : ExpressionEvaluates program size_condition_evaluates context evidence source
          environment before condition (.bool false) after) :
        StatementExecutes program (stepSize [size_condition_evaluates]) context evidence source environment before id
          context (.fallthrough environment) after
    | ifFalseWithElse
        {size_condition_evaluates size_body_executes : Nat}
        {context evidence source environment before middle after id node condition
          thenBody elseBody innerFinalContext outcome}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .ifThen condition thenBody (some elseBody))
        (condition_evaluates : ExpressionEvaluates program size_condition_evaluates context evidence source
          environment before condition (.bool false) middle)
        (body_executes : StatementsExecute program size_body_executes context evidence source
          environment middle elseBody innerFinalContext outcome after) :
        StatementExecutes program (stepSize [size_condition_evaluates, size_body_executes]) context evidence source environment before id
          context (restoreControl environment outcome) after
    | block
        {size_body_executes : Nat}
        {context evidence source environment before after id node body
          innerFinalContext outcome}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .block body)
        (body_executes : StatementsExecute program size_body_executes context evidence source
          environment before body innerFinalContext outcome after) :
        StatementExecutes program (stepSize [size_body_executes]) context evidence source environment before id
          context (restoreControl environment outcome) after
    | matchArm
        {size_scrutinee_evaluates size_execute : Nat}
        {context evidence source environment before scrutineeHeap hiddenHeap after
          id node resolution scrutinee scrutineeNode location armBody bindings
          binders values armContext armFinalContext armEnvironment bound outcome}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .matchWith resolution)
        (scrutinee_contains : ContainsExpression source resolution.scrutinee
          scrutineeNode)
        (scrutinee_evaluates : ExpressionEvaluates program size_scrutinee_evaluates context evidence source
          environment before resolution.scrutinee scrutinee scrutineeHeap)
        (allocate_hidden : Heap.Allocates scrutineeHeap scrutineeNode.type
          (some scrutinee) location hiddenHeap)
        (select : MatchCasesSelect context scrutinee resolution.cases
          resolution.defaultBody (.arm armBody bindings))
        (binders_eq : binders = bindings.map Prod.fst)
        (values_eq : values = bindings.map Prod.snd)
        (binders_extend : BindersExtend source.owner context binders armContext)
        (allocate_bindings : BindersAllocate environment hiddenHeap binders values
          armEnvironment bound)
        (execute : StatementsExecute program size_execute armContext evidence source armEnvironment
          bound armBody armFinalContext outcome after) :
        StatementExecutes program (stepSize [size_scrutinee_evaluates, size_execute]) context evidence source environment before id
          context (restoreControl environment outcome) after
    | matchDefault
        {size_scrutinee_evaluates size_execute : Nat}
        {context evidence source environment before scrutineeHeap hiddenHeap after
          id node resolution scrutinee scrutineeNode location defaultBody
          defaultFinalContext outcome}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .matchWith resolution)
        (scrutinee_contains : ContainsExpression source resolution.scrutinee
          scrutineeNode)
        (scrutinee_evaluates : ExpressionEvaluates program size_scrutinee_evaluates context evidence source
          environment before resolution.scrutinee scrutinee scrutineeHeap)
        (allocate_hidden : Heap.Allocates scrutineeHeap scrutineeNode.type
          (some scrutinee) location hiddenHeap)
        (select : MatchCasesSelect context scrutinee resolution.cases
          resolution.defaultBody (.default defaultBody))
        (execute : StatementsExecute program size_execute context evidence source environment
          hiddenHeap defaultBody defaultFinalContext outcome after) :
        StatementExecutes program (stepSize [size_scrutinee_evaluates, size_execute]) context evidence source environment before id
          context (restoreControl environment outcome) after
    | matchNoBranch
        {size_scrutinee_evaluates : Nat}
        {context evidence source environment before scrutineeHeap hiddenHeap id node
          resolution scrutinee scrutineeNode location}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .matchWith resolution)
        (scrutinee_contains : ContainsExpression source resolution.scrutinee
          scrutineeNode)
        (scrutinee_evaluates : ExpressionEvaluates program size_scrutinee_evaluates context evidence source
          environment before resolution.scrutinee scrutinee scrutineeHeap)
        (allocate_hidden : Heap.Allocates scrutineeHeap scrutineeNode.type
          (some scrutinee) location hiddenHeap)
        (select : MatchCasesSelect context scrutinee resolution.cases
          resolution.defaultBody .noBranch) :
        StatementExecutes program (stepSize [size_scrutinee_evaluates]) context evidence source environment before id
          context (.fallthrough environment) hiddenHeap
    | forLoop
        {size_initializer_executes size_iterate : Nat}
        {context evidence source environment before initialized after id node
          initializer condition post body loopContext loopFinalContext loopEnvironment
          outcome}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .forLoop initializer condition post body)
        (initializer_executes : ForItemsExecute program size_initializer_executes context evidence source
          environment before initializer loopContext loopEnvironment initialized)
        (iterate : ForLoopExecutes program size_iterate loopContext evidence source loopEnvironment
          initialized condition post body loopFinalContext outcome after) :
        StatementExecutes program (stepSize [size_initializer_executes, size_iterate]) context evidence source environment before id
          context (restoreControl environment outcome) after
    | whileLoop
        {size_iterate : Nat}
        {context evidence source environment before after id node condition body
          finalContext outcome}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .whileLoop condition body)
        (iterate : WhileExecutes program size_iterate context evidence source environment before
          condition body finalContext outcome after) :
        StatementExecutes program (stepSize [size_iterate]) context evidence source environment before id
          context (restoreControl environment outcome) after
    | breakStmt
        {context evidence source environment heap id node}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .breakStmt) :
        StatementExecutes program (stepSize []) context evidence source environment heap id
          context (.breaking environment) heap
    | continueStmt
        {context evidence source environment heap id node}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .continueStmt) :
        StatementExecutes program (stepSize []) context evidence source environment heap id
          context (.continuing environment) heap

  inductive StatementsExecute (program : Program) : Nat →
      Context → EvidenceEnvironment → TypedSource → Dynamic.Environment →
        Heap → List StatementId → Context → ControlOutcome → Heap → Prop where
    | nil
        {context evidence source environment heap} :
        StatementsExecute program (stepSize []) context evidence source environment heap []
          context (.fallthrough environment) heap
    | cons
        {size_head size_tail : Nat}
        {context middleContext finalContext evidence source environment before
          middle after statement statements nextEnvironment outcome}
        (head : StatementExecutes program size_head context evidence source environment before
          statement middleContext (.fallthrough nextEnvironment) middle)
        (tail : StatementsExecute program size_tail middleContext evidence source
          nextEnvironment middle statements finalContext outcome after) :
        StatementsExecute program (stepSize [size_head, size_tail]) context evidence source environment before
          (statement :: statements) finalContext outcome after
    | terminal
        {size_head : Nat}
        {context finalContext evidence source environment before after statement
          statements outcome}
        (head : StatementExecutes program size_head context evidence source environment before
          statement finalContext outcome after)
        (terminal : TerminalControl outcome) :
        StatementsExecute program (stepSize [size_head]) context evidence source environment before
          (statement :: statements) finalContext outcome after

  inductive FunctionStatementsExecute (program : Program) : Nat →
      Context → EvidenceEnvironment → TypedSource → Dynamic.Environment →
        Heap → List StatementId → Context → ControlOutcome → Heap → Prop where
    | nil
        {context evidence source environment heap} :
        FunctionStatementsExecute program (stepSize []) context evidence source environment heap
          [] context (.fallthrough environment) heap
    | tailExpression
        {size_evaluate : Nat}
        {context evidence source environment before after statement node expression
          value}
        (contains : ContainsStatement source statement node)
        (form_eq : node.form = .expression expression false)
        (evaluate : ExpressionEvaluates program size_evaluate context evidence source environment
          before expression value after) :
        FunctionStatementsExecute program (stepSize [size_evaluate]) context evidence source environment before
          [statement] context (.returned value) after
    | singleton
        {size_execute : Nat}
        {context finalContext evidence source environment before after statement node
          outcome}
        (contains : ContainsStatement source statement node)
        (not_tail : ∀ expression, node.form ≠ .expression expression false)
        (execute : StatementExecutes program size_execute context evidence source environment
          before statement finalContext outcome after) :
        FunctionStatementsExecute program (stepSize [size_execute]) context evidence source environment before
          [statement] finalContext outcome after
    | cons
        {size_head size_tail : Nat}
        {context middleContext finalContext evidence source environment before middle
          after statement next rest nextEnvironment outcome}
        (head : StatementExecutes program size_head context evidence source environment before
          statement middleContext (.fallthrough nextEnvironment) middle)
        (tail : FunctionStatementsExecute program size_tail middleContext evidence source
          nextEnvironment middle (next :: rest) finalContext outcome after) :
        FunctionStatementsExecute program (stepSize [size_head, size_tail]) context evidence source environment before
          (statement :: next :: rest) finalContext outcome after
    | terminal
        {size_head : Nat}
        {context finalContext evidence source environment before after statement next
          rest outcome}
        (head : StatementExecutes program size_head context evidence source environment before
          statement finalContext outcome after)
        (terminal : TerminalControl outcome) :
        FunctionStatementsExecute program (stepSize [size_head]) context evidence source environment before
          (statement :: next :: rest) finalContext outcome after

  inductive ForItemExecutes (program : Program) : Nat →
      Context → EvidenceEnvironment → TypedSource → Dynamic.Environment →
        Heap → ForItemForm → Context → Dynamic.Environment → Heap → Prop where
    | letUninitialized
        {context finalContext evidence source environment before after binder location}
        (monomorphic : binder.scheme.quantified = [])
        (extension : BinderExtends source.owner context binder finalContext)
        (allocate : Heap.Allocates before binder.scheme.body none location after) :
        ForItemExecutes program (stepSize []) context evidence source environment before
          (.letDecl binder none) finalContext
          ((binder.id, location) :: environment) after
    | letInitialized
        {size_evaluate : Nat}
        {context finalContext evidence source environment before middle after binder
          initializer value location}
        (evaluate : ExpressionEvaluates program size_evaluate context evidence source environment
          before initializer value middle)
        (monomorphic : binder.scheme.quantified = [])
        (extension : BinderExtends source.owner context binder finalContext)
        (allocate : Heap.Allocates middle binder.scheme.body (some value) location
          after) :
        ForItemExecutes program (stepSize [size_evaluate]) context evidence source environment before
          (.letDecl binder (some initializer)) finalContext
          ((binder.id, location) :: environment) after
    | letInitializedGeneralized
        {context finalContext evidence source environment before after binder
          initializer function location}
        (captures : GeneralizedClosureCaptures context source environment binder
          initializer function)
        (polymorphic : binder.scheme.quantified ≠ [])
        (extension : BinderExtends source.owner context binder finalContext)
        (allocate : Heap.AllocatesGeneralized before function location after) :
        ForItemExecutes program (stepSize []) context evidence source environment before
          (.letDecl binder (some initializer)) finalContext
          ((binder.id, location) :: environment) after
    | expression
        {size_evaluate : Nat}
        {context evidence source environment before after expression value}
        (evaluate : ExpressionEvaluates program size_evaluate context evidence source environment
          before expression value after) :
        ForItemExecutes program (stepSize [size_evaluate]) context evidence source environment before
          (.expression expression) context environment after
    | assignValue
        {size_execute : Nat}
        {context evidence source environment before after assignment operator rhs
          updatedRoot}
        (execute : SourcePlaceAssignment program size_execute context evidence source
          (AssignmentValueApplies operator) environment before assignment.target rhs
          updatedRoot after) :
        ForItemExecutes program (stepSize [size_execute]) context evidence source environment before
          (.assignValue assignment operator rhs) context environment after
    | assignBitNot
        {size_execute : Nat}
        {context evidence source environment before after assignment updatedRoot}
        (execute : SourcePlaceSnapshotUpdate program size_execute context evidence source
          BitNotSnapshot environment before assignment.target updatedRoot after) :
        ForItemExecutes program (stepSize [size_execute]) context evidence source environment before
          (.assignBitNot assignment) context environment after

  inductive ForItemsExecute (program : Program) : Nat →
      Context → EvidenceEnvironment → TypedSource → Dynamic.Environment →
        Heap → List ForItemForm → Context → Dynamic.Environment → Heap → Prop where
    | nil
        {context evidence source environment heap} :
        ForItemsExecute program (stepSize []) context evidence source environment heap []
          context environment heap
    | cons
        {size_head size_tail : Nat}
        {context middleContext finalContext evidence source environment before middle
          after item items nextEnvironment finalEnvironment}
        (head : ForItemExecutes program size_head context evidence source environment before
          item middleContext nextEnvironment middle)
        (tail : ForItemsExecute program size_tail middleContext evidence source nextEnvironment
          middle items finalContext finalEnvironment after) :
        ForItemsExecute program (stepSize [size_head, size_tail]) context evidence source environment before
          (item :: items) finalContext finalEnvironment after

  inductive WhileExecutes (program : Program) : Nat →
      Context → EvidenceEnvironment → TypedSource → Dynamic.Environment →
        Heap → ExpressionId → List StatementId →
        Context → ControlOutcome → Heap → Prop where
    | done
        {size_condition_evaluates : Nat}
        {context evidence source environment before after condition body}
        (condition_evaluates : ExpressionEvaluates program size_condition_evaluates context evidence source
          environment before condition (.bool false) after) :
        WhileExecutes program (stepSize [size_condition_evaluates]) context evidence source environment before condition
          body context (.fallthrough environment) after
    | nextFallthrough
        {size_condition_evaluates size_body_executes size_next : Nat}
        {context evidence source environment before conditionHeap bodyHeap after
          condition body bodyFinalContext bodyEnvironment outcome}
        (condition_evaluates : ExpressionEvaluates program size_condition_evaluates context evidence source
          environment before condition (.bool true) conditionHeap)
        (body_executes : StatementsExecute program size_body_executes context evidence source environment
          conditionHeap body bodyFinalContext (.fallthrough bodyEnvironment) bodyHeap)
        (next : WhileExecutes program size_next context evidence source environment bodyHeap
          condition body context outcome after) :
        WhileExecutes program (stepSize [size_condition_evaluates, size_body_executes, size_next]) context evidence source environment before condition
          body context outcome after
    | nextContinue
        {size_condition_evaluates size_body_executes size_next : Nat}
        {context evidence source environment before conditionHeap bodyHeap after
          condition body bodyFinalContext bodyEnvironment outcome}
        (condition_evaluates : ExpressionEvaluates program size_condition_evaluates context evidence source
          environment before condition (.bool true) conditionHeap)
        (body_executes : StatementsExecute program size_body_executes context evidence source environment
          conditionHeap body bodyFinalContext (.continuing bodyEnvironment) bodyHeap)
        (next : WhileExecutes program size_next context evidence source environment bodyHeap
          condition body context outcome after) :
        WhileExecutes program (stepSize [size_condition_evaluates, size_body_executes, size_next]) context evidence source environment before condition
          body context outcome after
    | breaks
        {size_condition_evaluates size_body_executes : Nat}
        {context evidence source environment before conditionHeap after condition
          body bodyFinalContext bodyEnvironment}
        (condition_evaluates : ExpressionEvaluates program size_condition_evaluates context evidence source
          environment before condition (.bool true) conditionHeap)
        (body_executes : StatementsExecute program size_body_executes context evidence source environment
          conditionHeap body bodyFinalContext (.breaking bodyEnvironment) after) :
        WhileExecutes program (stepSize [size_condition_evaluates, size_body_executes]) context evidence source environment before condition
          body context (.fallthrough environment) after
    | returns
        {size_condition_evaluates size_body_executes : Nat}
        {context evidence source environment before conditionHeap after condition
          body bodyFinalContext result}
        (condition_evaluates : ExpressionEvaluates program size_condition_evaluates context evidence source
          environment before condition (.bool true) conditionHeap)
        (body_executes : StatementsExecute program size_body_executes context evidence source environment
          conditionHeap body bodyFinalContext (.returned result) after) :
        WhileExecutes program (stepSize [size_condition_evaluates, size_body_executes]) context evidence source environment before condition
          body context (.returned result) after

  inductive ForLoopExecutes (program : Program) : Nat →
      Context → EvidenceEnvironment → TypedSource → Dynamic.Environment →
        Heap → ExpressionId → List ForItemForm → List StatementId →
        Context → ControlOutcome → Heap → Prop where
    | done
        {size_condition_evaluates : Nat}
        {context evidence source environment before after condition post body}
        (condition_evaluates : ExpressionEvaluates program size_condition_evaluates context evidence source
          environment before condition (.bool false) after) :
        ForLoopExecutes program (stepSize [size_condition_evaluates]) context evidence source environment before condition
          post body context (.fallthrough environment) after
    | nextFallthrough
        {size_condition_evaluates size_body_executes size_post_executes size_next : Nat}
        {context evidence source environment before conditionHeap bodyHeap postHeap
          after condition post body bodyFinalContext postFinalContext bodyEnvironment
          postEnvironment outcome}
        (condition_evaluates : ExpressionEvaluates program size_condition_evaluates context evidence source
          environment before condition (.bool true) conditionHeap)
        (body_executes : StatementsExecute program size_body_executes context evidence source environment
          conditionHeap body bodyFinalContext (.fallthrough bodyEnvironment) bodyHeap)
        (post_executes : ForItemsExecute program size_post_executes context evidence source environment
          bodyHeap post postFinalContext postEnvironment postHeap)
        (next : ForLoopExecutes program size_next context evidence source environment postHeap
          condition post body context outcome after) :
        ForLoopExecutes program (stepSize [size_condition_evaluates, size_body_executes, size_post_executes, size_next]) context evidence source environment before condition
          post body context outcome after
    | nextContinue
        {size_condition_evaluates size_body_executes size_post_executes size_next : Nat}
        {context evidence source environment before conditionHeap bodyHeap postHeap
          after condition post body bodyFinalContext postFinalContext bodyEnvironment
          postEnvironment outcome}
        (condition_evaluates : ExpressionEvaluates program size_condition_evaluates context evidence source
          environment before condition (.bool true) conditionHeap)
        (body_executes : StatementsExecute program size_body_executes context evidence source environment
          conditionHeap body bodyFinalContext (.continuing bodyEnvironment) bodyHeap)
        (post_executes : ForItemsExecute program size_post_executes context evidence source environment
          bodyHeap post postFinalContext postEnvironment postHeap)
        (next : ForLoopExecutes program size_next context evidence source environment postHeap
          condition post body context outcome after) :
        ForLoopExecutes program (stepSize [size_condition_evaluates, size_body_executes, size_post_executes, size_next]) context evidence source environment before condition
          post body context outcome after
    | breaks
        {size_condition_evaluates size_body_executes : Nat}
        {context evidence source environment before conditionHeap after condition post
          body bodyFinalContext bodyEnvironment}
        (condition_evaluates : ExpressionEvaluates program size_condition_evaluates context evidence source
          environment before condition (.bool true) conditionHeap)
        (body_executes : StatementsExecute program size_body_executes context evidence source environment
          conditionHeap body bodyFinalContext (.breaking bodyEnvironment) after) :
        ForLoopExecutes program (stepSize [size_condition_evaluates, size_body_executes]) context evidence source environment before condition
          post body context (.fallthrough environment) after
    | returns
        {size_condition_evaluates size_body_executes : Nat}
        {context evidence source environment before conditionHeap after condition post
          body bodyFinalContext result}
        (condition_evaluates : ExpressionEvaluates program size_condition_evaluates context evidence source
          environment before condition (.bool true) conditionHeap)
        (body_executes : StatementsExecute program size_body_executes context evidence source environment
          conditionHeap body bodyFinalContext (.returned result) after) :
        ForLoopExecutes program (stepSize [size_condition_evaluates, size_body_executes]) context evidence source environment before condition
          post body context (.returned result) after

end

mutual
theorem ExpressionEvaluates.sound {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : ExpressionId} {a6 : Value} {a7 : Heap}
    (trace : ExpressionEvaluates program size a0 a1 a2 a3 a4 a5 a6 a7) : Dynamic.ExpressionEvaluates program a0 a1 a2 a3 a4 a5 a6 a7 := by
  match trace with
  | .intro contains form coercions =>
    exact .intro contains (ExpressionFormEvaluates.sound form) (CoercionPathExecutes.sound coercions)
  | .generalizedLocal contains form_eq layout lookup read descriptor context_fields instantiation coercions =>
    exact .generalizedLocal contains form_eq layout lookup read descriptor context_fields instantiation (CoercionPathExecutes.sound coercions)
termination_by structural trace

theorem ExpressionFormEvaluates.sound {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : ExpressionForm} {a6 : List RequirementId} {a7 : List CoercionStep} {a8 : Value} {a9 : Heap}
    (trace : ExpressionFormEvaluates program size a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) : Dynamic.ExpressionFormEvaluates program a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 := by
  match trace with
  | .literal layout constructs =>
    exact .literal layout constructs
  | .integerLiteral layout constructs =>
    exact .integerLiteral layout constructs
  | .local layout lookup read descriptor_empty initialized =>
    exact .local layout lookup read descriptor_empty initialized
  | .localEmptyMapping layout lookup read descriptor_empty type_eq empty write =>
    exact .localEmptyMapping layout lookup read descriptor_empty type_eq empty write
  | .declaration layout valid requirements_close =>
    exact .declaration layout valid requirements_close
  | .builtinFunction layout =>
    exact .builtinFunction layout
  | .builtinBoolean layout =>
    exact .builtinBoolean layout
  | .group layout inner_evaluates =>
    exact .group layout (ExpressionEvaluates.sound inner_evaluates)
  | .tuple layout elements_evaluate pack =>
    exact .tuple layout (ExpressionsEvaluate.sound elements_evaluate) pack
  | .unary layout operand_evaluates applies =>
    exact .unary layout (ExpressionEvaluates.sound operand_evaluates) (UnaryOperationApplies.sound applies)
  | .binaryShortCircuit layout left_evaluates circuit owned_empty =>
    exact .binaryShortCircuit layout (ExpressionEvaluates.sound left_evaluates) circuit owned_empty
  | .binaryEvaluateRight layout left_evaluates evaluate_right right_evaluates applies =>
    exact .binaryEvaluateRight layout (ExpressionEvaluates.sound left_evaluates) evaluate_right (ExpressionEvaluates.sound right_evaluates) (BinaryOperationApplies.sound applies)
  | .conditionalTrue layout condition_evaluates branch_evaluates =>
    exact .conditionalTrue layout (ExpressionEvaluates.sound condition_evaluates) (ExpressionEvaluates.sound branch_evaluates)
  | .conditionalFalse layout condition_evaluates branch_evaluates =>
    exact .conditionalFalse layout (ExpressionEvaluates.sound condition_evaluates) (ExpressionEvaluates.sound branch_evaluates)
  | .lambda layout =>
    exact .lambda layout
  | .directCall callee_contains callee_form callee_requirements callee_coercions valid arguments_evaluate call_evidence applies =>
    exact .directCall callee_contains callee_form callee_requirements callee_coercions valid (ExpressionsEvaluate.sound arguments_evaluate) call_evidence (CallableApplies.sound applies)
  | .builtinCall layout arguments_evaluate applies =>
    exact .builtinCall layout (ExpressionsEvaluate.sound arguments_evaluate) (CallableApplies.sound applies)
  | .indirectCall requirements_eq callee_evaluates arguments_evaluate pack_before argument_coercions pack_after source_arity applied_arity applies =>
    exact .indirectCall requirements_eq (ExpressionEvaluates.sound callee_evaluates) (ExpressionsEvaluate.sound arguments_evaluate) pack_before (CoercionPathExecutes.sound argument_coercions) pack_after source_arity applied_arity (CallableApplies.sound applies)
  | .constructor layout valid arguments_evaluate =>
    exact .constructor layout valid (ExpressionsEvaluate.sound arguments_evaluate)
  | .member layout base_evaluates selected_at =>
    exact .member layout (ExpressionEvaluates.sound base_evaluates) selected_at
  | .proxy layout =>
    exact .proxy layout
  | .indexFound layout base_evaluates index_evaluates lookup =>
    exact .indexFound layout (ExpressionEvaluates.sound base_evaluates) (ExpressionEvaluates.sound index_evaluates) lookup
  | .indexDefault layout base_evaluates index_evaluates absent defaulted =>
    exact .indexDefault layout (ExpressionEvaluates.sound base_evaluates) (ExpressionEvaluates.sound index_evaluates) absent defaulted
termination_by structural trace

theorem ExpressionsEvaluate.sound {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : List ExpressionId} {a6 : List Value} {a7 : Heap}
    (trace : ExpressionsEvaluate program size a0 a1 a2 a3 a4 a5 a6 a7) : Dynamic.ExpressionsEvaluate program a0 a1 a2 a3 a4 a5 a6 a7 := by
  match trace with
  | .nil  =>
    exact .nil
  | .cons head tail =>
    exact .cons (ExpressionEvaluates.sound head) (ExpressionsEvaluate.sound tail)
termination_by structural trace

theorem SourceProjectionsEvaluate.sound {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : List PlaceProjection} {a6 : List EvaluatedProjection} {a7 : Heap}
    (trace : SourceProjectionsEvaluate program size a0 a1 a2 a3 a4 a5 a6 a7) : Dynamic.SourceProjectionsEvaluate program a0 a1 a2 a3 a4 a5 a6 a7 := by
  match trace with
  | .nil  =>
    exact .nil
  | .member tail =>
    exact .member (SourceProjectionsEvaluate.sound tail)
  | .index head tail =>
    exact .index (ExpressionEvaluates.sound head) (SourceProjectionsEvaluate.sound tail)
termination_by structural trace

theorem SourcePlaceResolves.sound {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : PlaceResolution} {a6 : ResolvedPlace} {a7 : Heap}
    (trace : SourcePlaceResolves program size a0 a1 a2 a3 a4 a5 a6 a7) : Dynamic.SourcePlaceResolves program a0 a1 a2 a3 a4 a5 a6 a7 := by
  match trace with
  | .intro root_lookup initial_read evaluate current_read initial_value selection =>
    exact .intro root_lookup initial_read (SourceProjectionsEvaluate.sound evaluate) current_read initial_value selection
termination_by structural trace

theorem SourcePlaceAssignment.sound {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : (Option Value → Value → Value → Prop)} {a4 : Dynamic.Environment} {a5 : Heap} {a6 : PlaceResolution} {a7 : ExpressionId} {a8 : Value} {a9 : Heap}
    (trace : SourcePlaceAssignment program size a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) : Dynamic.SourcePlaceAssignment program a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 := by
  match trace with
  | .intro resolve evaluate_right write =>
    exact .intro (SourcePlaceResolves.sound resolve) (ExpressionEvaluates.sound evaluate_right) write
termination_by structural trace

theorem SourcePlaceSnapshotUpdate.sound {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : (Option Value → Value → Prop)} {a4 : Dynamic.Environment} {a5 : Heap} {a6 : PlaceResolution} {a7 : Value} {a8 : Heap}
    (trace : SourcePlaceSnapshotUpdate program size a0 a1 a2 a3 a4 a5 a6 a7 a8) : Dynamic.SourcePlaceSnapshotUpdate program a0 a1 a2 a3 a4 a5 a6 a7 a8 := by
  match trace with
  | .intro resolve write =>
    exact .intro (SourcePlaceResolves.sound resolve) write
termination_by structural trace

theorem UnaryOperationApplies.sound {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : Heap} {a3 : Syntax.UnaryOp} {a4 : List RequirementId} {a5 : Value} {a6 : Value} {a7 : Heap}
    (trace : UnaryOperationApplies program size a0 a1 a2 a3 a4 a5 a6 a7) : Dynamic.UnaryOperationApplies program a0 a1 a2 a3 a4 a5 a6 a7 := by
  match trace with
  | .primitive applies =>
    exact .primitive applies
  | .method dispatch selected invokes =>
    exact .method dispatch selected (BodyInvokes.sound invokes)
termination_by structural trace

theorem BinaryOperationApplies.sound {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : Heap} {a3 : Syntax.BinaryOp} {a4 : List RequirementId} {a5 : Value} {a6 : Value} {a7 : Value} {a8 : Heap}
    (trace : BinaryOperationApplies program size a0 a1 a2 a3 a4 a5 a6 a7 a8) : Dynamic.BinaryOperationApplies program a0 a1 a2 a3 a4 a5 a6 a7 a8 := by
  match trace with
  | .primitive applies =>
    exact .primitive applies
  | .method dispatch selected invokes =>
    exact .method dispatch selected (BodyInvokes.sound invokes)
termination_by structural trace

theorem CoercionStepExecutes.sound {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : Heap} {a3 : CoercionStep} {a4 : Value} {a5 : Value} {a6 : Heap}
    (trace : CoercionStepExecutes program size a0 a1 a2 a3 a4 a5 a6) : Dynamic.CoercionStepExecutes program a0 a1 a2 a3 a4 a5 a6 := by
  match trace with
  | .primitive no_source_method applies =>
    exact .primitive no_source_method applies
  | .method selected invokes =>
    exact .method selected (BodyInvokes.sound invokes)
termination_by structural trace

theorem CoercionPathExecutes.sound {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : Heap} {a3 : List CoercionStep} {a4 : Value} {a5 : Value} {a6 : Heap}
    (trace : CoercionPathExecutes program size a0 a1 a2 a3 a4 a5 a6) : Dynamic.CoercionPathExecutes program a0 a1 a2 a3 a4 a5 a6 := by
  match trace with
  | .nil  =>
    exact .nil
  | .cons head tail =>
    exact .cons (CoercionStepExecutes.sound head) (CoercionPathExecutes.sound tail)
termination_by structural trace

theorem CallableApplies.sound {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : EvidenceEnvironment} {a3 : Heap} {a4 : Value} {a5 : List Value} {a6 : Value} {a7 : Heap}
    (trace : CallableApplies program size a0 a1 a2 a3 a4 a5 a6 a7) : Dynamic.CallableApplies program a0 a1 a2 a3 a4 a5 a6 a7 := by
  match trace with
  | .builtin applies =>
    exact .builtin applies
  | .global instantiates invocation_eq covers invokes =>
    exact .global instantiates invocation_eq covers (BodyInvokes.sound invokes)
  | .closure invocation_eq frame parameters_extend allocate execute returned =>
    exact .closure invocation_eq frame parameters_extend allocate (FunctionStatementsExecute.sound execute) returned
  | .closureUnit invocation_eq frame result_unit parameters_extend allocate execute fell_through =>
    exact .closureUnit invocation_eq frame result_unit parameters_extend allocate (FunctionStatementsExecute.sound execute) fell_through
termination_by structural trace

theorem BodyInvokes.sound {program : Program} {size : Nat} {a0 : BodyInstance} {a1 : EvidenceEnvironment} {a2 : Heap} {a3 : List Value} {a4 : Value} {a5 : Heap}
    (trace : BodyInvokes program size a0 a1 a2 a3 a4 a5) : Dynamic.BodyInvokes program a0 a1 a2 a3 a4 a5 := by
  match trace with
  | .returned covers roots_eq inputs_extend allocate execute returned =>
    exact .returned covers roots_eq inputs_extend allocate (FunctionStatementsExecute.sound execute) returned
  | .unit covers result_unit roots_eq inputs_extend allocate execute fell_through =>
    exact .unit covers result_unit roots_eq inputs_extend allocate (FunctionStatementsExecute.sound execute) fell_through
termination_by structural trace

theorem StatementExecutes.sound {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : StatementId} {a6 : Context} {a7 : ControlOutcome} {a8 : Heap}
    (trace : StatementExecutes program size a0 a1 a2 a3 a4 a5 a6 a7 a8) : Dynamic.StatementExecutes program a0 a1 a2 a3 a4 a5 a6 a7 a8 := by
  match trace with
  | .letUninitialized contains form_eq monomorphic extension allocate =>
    exact .letUninitialized contains form_eq monomorphic extension allocate
  | .letInitialized contains form_eq evaluate monomorphic extension allocate =>
    exact .letInitialized contains form_eq (ExpressionEvaluates.sound evaluate) monomorphic extension allocate
  | .letInitializedGeneralized contains form_eq captures polymorphic extension allocate =>
    exact .letInitializedGeneralized contains form_eq captures polymorphic extension allocate
  | .returnUnit contains form_eq =>
    exact .returnUnit contains form_eq
  | .returnValue contains form_eq evaluate =>
    exact .returnValue contains form_eq (ExpressionEvaluates.sound evaluate)
  | .expression contains form_eq evaluate =>
    exact .expression contains form_eq (ExpressionEvaluates.sound evaluate)
  | .assignValue contains form_eq assignment_executes =>
    exact .assignValue contains form_eq (SourcePlaceAssignment.sound assignment_executes)
  | .assignBitNot contains form_eq assignment_executes =>
    exact .assignBitNot contains form_eq (SourcePlaceSnapshotUpdate.sound assignment_executes)
  | .ifTrue contains form_eq condition_evaluates body_executes =>
    exact .ifTrue contains form_eq (ExpressionEvaluates.sound condition_evaluates) (StatementsExecute.sound body_executes)
  | .ifFalseWithoutElse contains form_eq condition_evaluates =>
    exact .ifFalseWithoutElse contains form_eq (ExpressionEvaluates.sound condition_evaluates)
  | .ifFalseWithElse contains form_eq condition_evaluates body_executes =>
    exact .ifFalseWithElse contains form_eq (ExpressionEvaluates.sound condition_evaluates) (StatementsExecute.sound body_executes)
  | .block contains form_eq body_executes =>
    exact .block contains form_eq (StatementsExecute.sound body_executes)
  | .matchArm contains form_eq scrutinee_contains scrutinee_evaluates allocate_hidden select binders_eq values_eq binders_extend allocate_bindings execute =>
    exact .matchArm contains form_eq scrutinee_contains (ExpressionEvaluates.sound scrutinee_evaluates) allocate_hidden select binders_eq values_eq binders_extend allocate_bindings (StatementsExecute.sound execute)
  | .matchDefault contains form_eq scrutinee_contains scrutinee_evaluates allocate_hidden select execute =>
    exact .matchDefault contains form_eq scrutinee_contains (ExpressionEvaluates.sound scrutinee_evaluates) allocate_hidden select (StatementsExecute.sound execute)
  | .matchNoBranch contains form_eq scrutinee_contains scrutinee_evaluates allocate_hidden select =>
    exact .matchNoBranch contains form_eq scrutinee_contains (ExpressionEvaluates.sound scrutinee_evaluates) allocate_hidden select
  | .forLoop contains form_eq initializer_executes iterate =>
    exact .forLoop contains form_eq (ForItemsExecute.sound initializer_executes) (ForLoopExecutes.sound iterate)
  | .whileLoop contains form_eq iterate =>
    exact .whileLoop contains form_eq (WhileExecutes.sound iterate)
  | .breakStmt contains form_eq =>
    exact .breakStmt contains form_eq
  | .continueStmt contains form_eq =>
    exact .continueStmt contains form_eq
termination_by structural trace

theorem StatementsExecute.sound {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : List StatementId} {a6 : Context} {a7 : ControlOutcome} {a8 : Heap}
    (trace : StatementsExecute program size a0 a1 a2 a3 a4 a5 a6 a7 a8) : Dynamic.StatementsExecute program a0 a1 a2 a3 a4 a5 a6 a7 a8 := by
  match trace with
  | .nil  =>
    exact .nil
  | .cons head tail =>
    exact .cons (StatementExecutes.sound head) (StatementsExecute.sound tail)
  | .terminal head terminal =>
    exact .terminal (StatementExecutes.sound head) terminal
termination_by structural trace

theorem FunctionStatementsExecute.sound {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : List StatementId} {a6 : Context} {a7 : ControlOutcome} {a8 : Heap}
    (trace : FunctionStatementsExecute program size a0 a1 a2 a3 a4 a5 a6 a7 a8) : Dynamic.FunctionStatementsExecute program a0 a1 a2 a3 a4 a5 a6 a7 a8 := by
  match trace with
  | .nil  =>
    exact .nil
  | .tailExpression contains form_eq evaluate =>
    exact .tailExpression contains form_eq (ExpressionEvaluates.sound evaluate)
  | .singleton contains not_tail execute =>
    exact .singleton contains not_tail (StatementExecutes.sound execute)
  | .cons head tail =>
    exact .cons (StatementExecutes.sound head) (FunctionStatementsExecute.sound tail)
  | .terminal head terminal =>
    exact .terminal (StatementExecutes.sound head) terminal
termination_by structural trace

theorem ForItemExecutes.sound {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : ForItemForm} {a6 : Context} {a7 : Dynamic.Environment} {a8 : Heap}
    (trace : ForItemExecutes program size a0 a1 a2 a3 a4 a5 a6 a7 a8) : Dynamic.ForItemExecutes program a0 a1 a2 a3 a4 a5 a6 a7 a8 := by
  match trace with
  | .letUninitialized monomorphic extension allocate =>
    exact .letUninitialized monomorphic extension allocate
  | .letInitialized evaluate monomorphic extension allocate =>
    exact .letInitialized (ExpressionEvaluates.sound evaluate) monomorphic extension allocate
  | .letInitializedGeneralized captures polymorphic extension allocate =>
    exact .letInitializedGeneralized captures polymorphic extension allocate
  | .expression evaluate =>
    exact .expression (ExpressionEvaluates.sound evaluate)
  | .assignValue execute =>
    exact .assignValue (SourcePlaceAssignment.sound execute)
  | .assignBitNot execute =>
    exact .assignBitNot (SourcePlaceSnapshotUpdate.sound execute)
termination_by structural trace

theorem ForItemsExecute.sound {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : List ForItemForm} {a6 : Context} {a7 : Dynamic.Environment} {a8 : Heap}
    (trace : ForItemsExecute program size a0 a1 a2 a3 a4 a5 a6 a7 a8) : Dynamic.ForItemsExecute program a0 a1 a2 a3 a4 a5 a6 a7 a8 := by
  match trace with
  | .nil  =>
    exact .nil
  | .cons head tail =>
    exact .cons (ForItemExecutes.sound head) (ForItemsExecute.sound tail)
termination_by structural trace

theorem WhileExecutes.sound {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : ExpressionId} {a6 : List StatementId} {a7 : Context} {a8 : ControlOutcome} {a9 : Heap}
    (trace : WhileExecutes program size a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) : Dynamic.WhileExecutes program a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 := by
  match trace with
  | .done condition_evaluates =>
    exact .done (ExpressionEvaluates.sound condition_evaluates)
  | .nextFallthrough condition_evaluates body_executes next =>
    exact .nextFallthrough (ExpressionEvaluates.sound condition_evaluates) (StatementsExecute.sound body_executes) (WhileExecutes.sound next)
  | .nextContinue condition_evaluates body_executes next =>
    exact .nextContinue (ExpressionEvaluates.sound condition_evaluates) (StatementsExecute.sound body_executes) (WhileExecutes.sound next)
  | .breaks condition_evaluates body_executes =>
    exact .breaks (ExpressionEvaluates.sound condition_evaluates) (StatementsExecute.sound body_executes)
  | .returns condition_evaluates body_executes =>
    exact .returns (ExpressionEvaluates.sound condition_evaluates) (StatementsExecute.sound body_executes)
termination_by structural trace

theorem ForLoopExecutes.sound {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : ExpressionId} {a6 : List ForItemForm} {a7 : List StatementId} {a8 : Context} {a9 : ControlOutcome} {a10 : Heap}
    (trace : ForLoopExecutes program size a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10) : Dynamic.ForLoopExecutes program a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 := by
  match trace with
  | .done condition_evaluates =>
    exact .done (ExpressionEvaluates.sound condition_evaluates)
  | .nextFallthrough condition_evaluates body_executes post_executes next =>
    exact .nextFallthrough (ExpressionEvaluates.sound condition_evaluates) (StatementsExecute.sound body_executes) (ForItemsExecute.sound post_executes) (ForLoopExecutes.sound next)
  | .nextContinue condition_evaluates body_executes post_executes next =>
    exact .nextContinue (ExpressionEvaluates.sound condition_evaluates) (StatementsExecute.sound body_executes) (ForItemsExecute.sound post_executes) (ForLoopExecutes.sound next)
  | .breaks condition_evaluates body_executes =>
    exact .breaks (ExpressionEvaluates.sound condition_evaluates) (StatementsExecute.sound body_executes)
  | .returns condition_evaluates body_executes =>
    exact .returns (ExpressionEvaluates.sound condition_evaluates) (StatementsExecute.sound body_executes)
termination_by structural trace

end

mutual
theorem ExpressionEvaluates.has_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : ExpressionId} {a6 : Value} {a7 : Heap}
    (trace : Dynamic.ExpressionEvaluates program a0 a1 a2 a3 a4 a5 a6 a7) : ∃ size, ExpressionEvaluates program size a0 a1 a2 a3 a4 a5 a6 a7 := by
  match trace with
  | .intro contains form coercions =>
    obtain ⟨size_form, form⟩ := ExpressionFormEvaluates.has_size form
    obtain ⟨size_coercions, coercions⟩ := CoercionPathExecutes.has_size coercions
    exact ⟨_, .intro contains form coercions⟩
  | .generalizedLocal contains form_eq layout lookup read descriptor context_fields instantiation coercions =>
    obtain ⟨size_coercions, coercions⟩ := CoercionPathExecutes.has_size coercions
    exact ⟨_, .generalizedLocal contains form_eq layout lookup read descriptor context_fields instantiation coercions⟩
termination_by structural trace

theorem ExpressionFormEvaluates.has_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : ExpressionForm} {a6 : List RequirementId} {a7 : List CoercionStep} {a8 : Value} {a9 : Heap}
    (trace : Dynamic.ExpressionFormEvaluates program a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) : ∃ size, ExpressionFormEvaluates program size a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 := by
  match trace with
  | .literal layout constructs =>
    exact ⟨_, .literal layout constructs⟩
  | .integerLiteral layout constructs =>
    exact ⟨_, .integerLiteral layout constructs⟩
  | .local layout lookup read descriptor_empty initialized =>
    exact ⟨_, .local layout lookup read descriptor_empty initialized⟩
  | .localEmptyMapping layout lookup read descriptor_empty type_eq empty write =>
    exact ⟨_, .localEmptyMapping layout lookup read descriptor_empty type_eq empty write⟩
  | .declaration layout valid requirements_close =>
    exact ⟨_, .declaration layout valid requirements_close⟩
  | .builtinFunction layout =>
    exact ⟨_, .builtinFunction layout⟩
  | .builtinBoolean layout =>
    exact ⟨_, .builtinBoolean layout⟩
  | .group layout inner_evaluates =>
    obtain ⟨size_inner_evaluates, inner_evaluates⟩ := ExpressionEvaluates.has_size inner_evaluates
    exact ⟨_, .group layout inner_evaluates⟩
  | .tuple layout elements_evaluate pack =>
    obtain ⟨size_elements_evaluate, elements_evaluate⟩ := ExpressionsEvaluate.has_size elements_evaluate
    exact ⟨_, .tuple layout elements_evaluate pack⟩
  | .unary layout operand_evaluates applies =>
    obtain ⟨size_operand_evaluates, operand_evaluates⟩ := ExpressionEvaluates.has_size operand_evaluates
    obtain ⟨size_applies, applies⟩ := UnaryOperationApplies.has_size applies
    exact ⟨_, .unary layout operand_evaluates applies⟩
  | .binaryShortCircuit layout left_evaluates circuit owned_empty =>
    obtain ⟨size_left_evaluates, left_evaluates⟩ := ExpressionEvaluates.has_size left_evaluates
    exact ⟨_, .binaryShortCircuit layout left_evaluates circuit owned_empty⟩
  | .binaryEvaluateRight layout left_evaluates evaluate_right right_evaluates applies =>
    obtain ⟨size_left_evaluates, left_evaluates⟩ := ExpressionEvaluates.has_size left_evaluates
    obtain ⟨size_right_evaluates, right_evaluates⟩ := ExpressionEvaluates.has_size right_evaluates
    obtain ⟨size_applies, applies⟩ := BinaryOperationApplies.has_size applies
    exact ⟨_, .binaryEvaluateRight layout left_evaluates evaluate_right right_evaluates applies⟩
  | .conditionalTrue layout condition_evaluates branch_evaluates =>
    obtain ⟨size_condition_evaluates, condition_evaluates⟩ := ExpressionEvaluates.has_size condition_evaluates
    obtain ⟨size_branch_evaluates, branch_evaluates⟩ := ExpressionEvaluates.has_size branch_evaluates
    exact ⟨_, .conditionalTrue layout condition_evaluates branch_evaluates⟩
  | .conditionalFalse layout condition_evaluates branch_evaluates =>
    obtain ⟨size_condition_evaluates, condition_evaluates⟩ := ExpressionEvaluates.has_size condition_evaluates
    obtain ⟨size_branch_evaluates, branch_evaluates⟩ := ExpressionEvaluates.has_size branch_evaluates
    exact ⟨_, .conditionalFalse layout condition_evaluates branch_evaluates⟩
  | .lambda layout =>
    exact ⟨_, .lambda layout⟩
  | .directCall callee_contains callee_form callee_requirements callee_coercions valid arguments_evaluate call_evidence applies =>
    obtain ⟨size_arguments_evaluate, arguments_evaluate⟩ := ExpressionsEvaluate.has_size arguments_evaluate
    obtain ⟨size_applies, applies⟩ := CallableApplies.has_size applies
    exact ⟨_, .directCall callee_contains callee_form callee_requirements callee_coercions valid arguments_evaluate call_evidence applies⟩
  | .builtinCall layout arguments_evaluate applies =>
    obtain ⟨size_arguments_evaluate, arguments_evaluate⟩ := ExpressionsEvaluate.has_size arguments_evaluate
    obtain ⟨size_applies, applies⟩ := CallableApplies.has_size applies
    exact ⟨_, .builtinCall layout arguments_evaluate applies⟩
  | .indirectCall requirements_eq callee_evaluates arguments_evaluate pack_before argument_coercions pack_after source_arity applied_arity applies =>
    obtain ⟨size_callee_evaluates, callee_evaluates⟩ := ExpressionEvaluates.has_size callee_evaluates
    obtain ⟨size_arguments_evaluate, arguments_evaluate⟩ := ExpressionsEvaluate.has_size arguments_evaluate
    obtain ⟨size_argument_coercions, argument_coercions⟩ := CoercionPathExecutes.has_size argument_coercions
    obtain ⟨size_applies, applies⟩ := CallableApplies.has_size applies
    exact ⟨_, .indirectCall requirements_eq callee_evaluates arguments_evaluate pack_before argument_coercions pack_after source_arity applied_arity applies⟩
  | .constructor layout valid arguments_evaluate =>
    obtain ⟨size_arguments_evaluate, arguments_evaluate⟩ := ExpressionsEvaluate.has_size arguments_evaluate
    exact ⟨_, .constructor layout valid arguments_evaluate⟩
  | .member layout base_evaluates selected_at =>
    obtain ⟨size_base_evaluates, base_evaluates⟩ := ExpressionEvaluates.has_size base_evaluates
    exact ⟨_, .member layout base_evaluates selected_at⟩
  | .proxy layout =>
    exact ⟨_, .proxy layout⟩
  | .indexFound layout base_evaluates index_evaluates lookup =>
    obtain ⟨size_base_evaluates, base_evaluates⟩ := ExpressionEvaluates.has_size base_evaluates
    obtain ⟨size_index_evaluates, index_evaluates⟩ := ExpressionEvaluates.has_size index_evaluates
    exact ⟨_, .indexFound layout base_evaluates index_evaluates lookup⟩
  | .indexDefault layout base_evaluates index_evaluates absent defaulted =>
    obtain ⟨size_base_evaluates, base_evaluates⟩ := ExpressionEvaluates.has_size base_evaluates
    obtain ⟨size_index_evaluates, index_evaluates⟩ := ExpressionEvaluates.has_size index_evaluates
    exact ⟨_, .indexDefault layout base_evaluates index_evaluates absent defaulted⟩
termination_by structural trace

theorem ExpressionsEvaluate.has_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : List ExpressionId} {a6 : List Value} {a7 : Heap}
    (trace : Dynamic.ExpressionsEvaluate program a0 a1 a2 a3 a4 a5 a6 a7) : ∃ size, ExpressionsEvaluate program size a0 a1 a2 a3 a4 a5 a6 a7 := by
  match trace with
  | .nil  =>
    exact ⟨_, .nil ⟩
  | .cons head tail =>
    obtain ⟨size_head, head⟩ := ExpressionEvaluates.has_size head
    obtain ⟨size_tail, tail⟩ := ExpressionsEvaluate.has_size tail
    exact ⟨_, .cons head tail⟩
termination_by structural trace

theorem SourceProjectionsEvaluate.has_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : List PlaceProjection} {a6 : List EvaluatedProjection} {a7 : Heap}
    (trace : Dynamic.SourceProjectionsEvaluate program a0 a1 a2 a3 a4 a5 a6 a7) : ∃ size, SourceProjectionsEvaluate program size a0 a1 a2 a3 a4 a5 a6 a7 := by
  match trace with
  | .nil  =>
    exact ⟨_, .nil ⟩
  | .member tail =>
    obtain ⟨size_tail, tail⟩ := SourceProjectionsEvaluate.has_size tail
    exact ⟨_, .member tail⟩
  | .index head tail =>
    obtain ⟨size_head, head⟩ := ExpressionEvaluates.has_size head
    obtain ⟨size_tail, tail⟩ := SourceProjectionsEvaluate.has_size tail
    exact ⟨_, .index head tail⟩
termination_by structural trace

theorem SourcePlaceResolves.has_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : PlaceResolution} {a6 : ResolvedPlace} {a7 : Heap}
    (trace : Dynamic.SourcePlaceResolves program a0 a1 a2 a3 a4 a5 a6 a7) : ∃ size, SourcePlaceResolves program size a0 a1 a2 a3 a4 a5 a6 a7 := by
  match trace with
  | .intro root_lookup initial_read evaluate current_read initial_value selection =>
    obtain ⟨size_evaluate, evaluate⟩ := SourceProjectionsEvaluate.has_size evaluate
    exact ⟨_, .intro root_lookup initial_read evaluate current_read initial_value selection⟩
termination_by structural trace

theorem SourcePlaceAssignment.has_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : (Option Value → Value → Value → Prop)} {a4 : Dynamic.Environment} {a5 : Heap} {a6 : PlaceResolution} {a7 : ExpressionId} {a8 : Value} {a9 : Heap}
    (trace : Dynamic.SourcePlaceAssignment program a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) : ∃ size, SourcePlaceAssignment program size a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 := by
  match trace with
  | .intro resolve evaluate_right write =>
    obtain ⟨size_resolve, resolve⟩ := SourcePlaceResolves.has_size resolve
    obtain ⟨size_evaluate_right, evaluate_right⟩ := ExpressionEvaluates.has_size evaluate_right
    exact ⟨_, .intro resolve evaluate_right write⟩
termination_by structural trace

theorem SourcePlaceSnapshotUpdate.has_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : (Option Value → Value → Prop)} {a4 : Dynamic.Environment} {a5 : Heap} {a6 : PlaceResolution} {a7 : Value} {a8 : Heap}
    (trace : Dynamic.SourcePlaceSnapshotUpdate program a0 a1 a2 a3 a4 a5 a6 a7 a8) : ∃ size, SourcePlaceSnapshotUpdate program size a0 a1 a2 a3 a4 a5 a6 a7 a8 := by
  match trace with
  | .intro resolve write =>
    obtain ⟨size_resolve, resolve⟩ := SourcePlaceResolves.has_size resolve
    exact ⟨_, .intro resolve write⟩
termination_by structural trace

theorem UnaryOperationApplies.has_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : Heap} {a3 : Syntax.UnaryOp} {a4 : List RequirementId} {a5 : Value} {a6 : Value} {a7 : Heap}
    (trace : Dynamic.UnaryOperationApplies program a0 a1 a2 a3 a4 a5 a6 a7) : ∃ size, UnaryOperationApplies program size a0 a1 a2 a3 a4 a5 a6 a7 := by
  match trace with
  | .primitive applies =>
    exact ⟨_, .primitive applies⟩
  | .method dispatch selected invokes =>
    obtain ⟨size_invokes, invokes⟩ := BodyInvokes.has_size invokes
    exact ⟨_, .method dispatch selected invokes⟩
termination_by structural trace

theorem BinaryOperationApplies.has_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : Heap} {a3 : Syntax.BinaryOp} {a4 : List RequirementId} {a5 : Value} {a6 : Value} {a7 : Value} {a8 : Heap}
    (trace : Dynamic.BinaryOperationApplies program a0 a1 a2 a3 a4 a5 a6 a7 a8) : ∃ size, BinaryOperationApplies program size a0 a1 a2 a3 a4 a5 a6 a7 a8 := by
  match trace with
  | .primitive applies =>
    exact ⟨_, .primitive applies⟩
  | .method dispatch selected invokes =>
    obtain ⟨size_invokes, invokes⟩ := BodyInvokes.has_size invokes
    exact ⟨_, .method dispatch selected invokes⟩
termination_by structural trace

theorem CoercionStepExecutes.has_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : Heap} {a3 : CoercionStep} {a4 : Value} {a5 : Value} {a6 : Heap}
    (trace : Dynamic.CoercionStepExecutes program a0 a1 a2 a3 a4 a5 a6) : ∃ size, CoercionStepExecutes program size a0 a1 a2 a3 a4 a5 a6 := by
  match trace with
  | .primitive no_source_method applies =>
    exact ⟨_, .primitive no_source_method applies⟩
  | .method selected invokes =>
    obtain ⟨size_invokes, invokes⟩ := BodyInvokes.has_size invokes
    exact ⟨_, .method selected invokes⟩
termination_by structural trace

theorem CoercionPathExecutes.has_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : Heap} {a3 : List CoercionStep} {a4 : Value} {a5 : Value} {a6 : Heap}
    (trace : Dynamic.CoercionPathExecutes program a0 a1 a2 a3 a4 a5 a6) : ∃ size, CoercionPathExecutes program size a0 a1 a2 a3 a4 a5 a6 := by
  match trace with
  | .nil  =>
    exact ⟨_, .nil ⟩
  | .cons head tail =>
    obtain ⟨size_head, head⟩ := CoercionStepExecutes.has_size head
    obtain ⟨size_tail, tail⟩ := CoercionPathExecutes.has_size tail
    exact ⟨_, .cons head tail⟩
termination_by structural trace

theorem CallableApplies.has_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : EvidenceEnvironment} {a3 : Heap} {a4 : Value} {a5 : List Value} {a6 : Value} {a7 : Heap}
    (trace : Dynamic.CallableApplies program a0 a1 a2 a3 a4 a5 a6 a7) : ∃ size, CallableApplies program size a0 a1 a2 a3 a4 a5 a6 a7 := by
  match trace with
  | .builtin applies =>
    exact ⟨_, .builtin applies⟩
  | .global instantiates invocation_eq covers invokes =>
    obtain ⟨size_invokes, invokes⟩ := BodyInvokes.has_size invokes
    exact ⟨_, .global instantiates invocation_eq covers invokes⟩
  | .closure invocation_eq frame parameters_extend allocate execute returned =>
    obtain ⟨size_execute, execute⟩ := FunctionStatementsExecute.has_size execute
    exact ⟨_, .closure invocation_eq frame parameters_extend allocate execute returned⟩
  | .closureUnit invocation_eq frame result_unit parameters_extend allocate execute fell_through =>
    obtain ⟨size_execute, execute⟩ := FunctionStatementsExecute.has_size execute
    exact ⟨_, .closureUnit invocation_eq frame result_unit parameters_extend allocate execute fell_through⟩
termination_by structural trace

theorem BodyInvokes.has_size {program : Program} {a0 : BodyInstance} {a1 : EvidenceEnvironment} {a2 : Heap} {a3 : List Value} {a4 : Value} {a5 : Heap}
    (trace : Dynamic.BodyInvokes program a0 a1 a2 a3 a4 a5) : ∃ size, BodyInvokes program size a0 a1 a2 a3 a4 a5 := by
  match trace with
  | .returned covers roots_eq inputs_extend allocate execute returned =>
    obtain ⟨size_execute, execute⟩ := FunctionStatementsExecute.has_size execute
    exact ⟨_, .returned covers roots_eq inputs_extend allocate execute returned⟩
  | .unit covers result_unit roots_eq inputs_extend allocate execute fell_through =>
    obtain ⟨size_execute, execute⟩ := FunctionStatementsExecute.has_size execute
    exact ⟨_, .unit covers result_unit roots_eq inputs_extend allocate execute fell_through⟩
termination_by structural trace

theorem StatementExecutes.has_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : StatementId} {a6 : Context} {a7 : ControlOutcome} {a8 : Heap}
    (trace : Dynamic.StatementExecutes program a0 a1 a2 a3 a4 a5 a6 a7 a8) : ∃ size, StatementExecutes program size a0 a1 a2 a3 a4 a5 a6 a7 a8 := by
  match trace with
  | .letUninitialized contains form_eq monomorphic extension allocate =>
    exact ⟨_, .letUninitialized contains form_eq monomorphic extension allocate⟩
  | .letInitialized contains form_eq evaluate monomorphic extension allocate =>
    obtain ⟨size_evaluate, evaluate⟩ := ExpressionEvaluates.has_size evaluate
    exact ⟨_, .letInitialized contains form_eq evaluate monomorphic extension allocate⟩
  | .letInitializedGeneralized contains form_eq captures polymorphic extension allocate =>
    exact ⟨_, .letInitializedGeneralized contains form_eq captures polymorphic extension allocate⟩
  | .returnUnit contains form_eq =>
    exact ⟨_, .returnUnit contains form_eq⟩
  | .returnValue contains form_eq evaluate =>
    obtain ⟨size_evaluate, evaluate⟩ := ExpressionEvaluates.has_size evaluate
    exact ⟨_, .returnValue contains form_eq evaluate⟩
  | .expression contains form_eq evaluate =>
    obtain ⟨size_evaluate, evaluate⟩ := ExpressionEvaluates.has_size evaluate
    exact ⟨_, .expression contains form_eq evaluate⟩
  | .assignValue contains form_eq assignment_executes =>
    obtain ⟨size_assignment_executes, assignment_executes⟩ := SourcePlaceAssignment.has_size assignment_executes
    exact ⟨_, .assignValue contains form_eq assignment_executes⟩
  | .assignBitNot contains form_eq assignment_executes =>
    obtain ⟨size_assignment_executes, assignment_executes⟩ := SourcePlaceSnapshotUpdate.has_size assignment_executes
    exact ⟨_, .assignBitNot contains form_eq assignment_executes⟩
  | .ifTrue contains form_eq condition_evaluates body_executes =>
    obtain ⟨size_condition_evaluates, condition_evaluates⟩ := ExpressionEvaluates.has_size condition_evaluates
    obtain ⟨size_body_executes, body_executes⟩ := StatementsExecute.has_size body_executes
    exact ⟨_, .ifTrue contains form_eq condition_evaluates body_executes⟩
  | .ifFalseWithoutElse contains form_eq condition_evaluates =>
    obtain ⟨size_condition_evaluates, condition_evaluates⟩ := ExpressionEvaluates.has_size condition_evaluates
    exact ⟨_, .ifFalseWithoutElse contains form_eq condition_evaluates⟩
  | .ifFalseWithElse contains form_eq condition_evaluates body_executes =>
    obtain ⟨size_condition_evaluates, condition_evaluates⟩ := ExpressionEvaluates.has_size condition_evaluates
    obtain ⟨size_body_executes, body_executes⟩ := StatementsExecute.has_size body_executes
    exact ⟨_, .ifFalseWithElse contains form_eq condition_evaluates body_executes⟩
  | .block contains form_eq body_executes =>
    obtain ⟨size_body_executes, body_executes⟩ := StatementsExecute.has_size body_executes
    exact ⟨_, .block contains form_eq body_executes⟩
  | .matchArm contains form_eq scrutinee_contains scrutinee_evaluates allocate_hidden select binders_eq values_eq binders_extend allocate_bindings execute =>
    obtain ⟨size_scrutinee_evaluates, scrutinee_evaluates⟩ := ExpressionEvaluates.has_size scrutinee_evaluates
    obtain ⟨size_execute, execute⟩ := StatementsExecute.has_size execute
    exact ⟨_, .matchArm contains form_eq scrutinee_contains scrutinee_evaluates allocate_hidden select binders_eq values_eq binders_extend allocate_bindings execute⟩
  | .matchDefault contains form_eq scrutinee_contains scrutinee_evaluates allocate_hidden select execute =>
    obtain ⟨size_scrutinee_evaluates, scrutinee_evaluates⟩ := ExpressionEvaluates.has_size scrutinee_evaluates
    obtain ⟨size_execute, execute⟩ := StatementsExecute.has_size execute
    exact ⟨_, .matchDefault contains form_eq scrutinee_contains scrutinee_evaluates allocate_hidden select execute⟩
  | .matchNoBranch contains form_eq scrutinee_contains scrutinee_evaluates allocate_hidden select =>
    obtain ⟨size_scrutinee_evaluates, scrutinee_evaluates⟩ := ExpressionEvaluates.has_size scrutinee_evaluates
    exact ⟨_, .matchNoBranch contains form_eq scrutinee_contains scrutinee_evaluates allocate_hidden select⟩
  | .forLoop contains form_eq initializer_executes iterate =>
    obtain ⟨size_initializer_executes, initializer_executes⟩ := ForItemsExecute.has_size initializer_executes
    obtain ⟨size_iterate, iterate⟩ := ForLoopExecutes.has_size iterate
    exact ⟨_, .forLoop contains form_eq initializer_executes iterate⟩
  | .whileLoop contains form_eq iterate =>
    obtain ⟨size_iterate, iterate⟩ := WhileExecutes.has_size iterate
    exact ⟨_, .whileLoop contains form_eq iterate⟩
  | .breakStmt contains form_eq =>
    exact ⟨_, .breakStmt contains form_eq⟩
  | .continueStmt contains form_eq =>
    exact ⟨_, .continueStmt contains form_eq⟩
termination_by structural trace

theorem StatementsExecute.has_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : List StatementId} {a6 : Context} {a7 : ControlOutcome} {a8 : Heap}
    (trace : Dynamic.StatementsExecute program a0 a1 a2 a3 a4 a5 a6 a7 a8) : ∃ size, StatementsExecute program size a0 a1 a2 a3 a4 a5 a6 a7 a8 := by
  match trace with
  | .nil  =>
    exact ⟨_, .nil ⟩
  | .cons head tail =>
    obtain ⟨size_head, head⟩ := StatementExecutes.has_size head
    obtain ⟨size_tail, tail⟩ := StatementsExecute.has_size tail
    exact ⟨_, .cons head tail⟩
  | .terminal head terminal =>
    obtain ⟨size_head, head⟩ := StatementExecutes.has_size head
    exact ⟨_, .terminal head terminal⟩
termination_by structural trace

theorem FunctionStatementsExecute.has_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : List StatementId} {a6 : Context} {a7 : ControlOutcome} {a8 : Heap}
    (trace : Dynamic.FunctionStatementsExecute program a0 a1 a2 a3 a4 a5 a6 a7 a8) : ∃ size, FunctionStatementsExecute program size a0 a1 a2 a3 a4 a5 a6 a7 a8 := by
  match trace with
  | .nil  =>
    exact ⟨_, .nil ⟩
  | .tailExpression contains form_eq evaluate =>
    obtain ⟨size_evaluate, evaluate⟩ := ExpressionEvaluates.has_size evaluate
    exact ⟨_, .tailExpression contains form_eq evaluate⟩
  | .singleton contains not_tail execute =>
    obtain ⟨size_execute, execute⟩ := StatementExecutes.has_size execute
    exact ⟨_, .singleton contains not_tail execute⟩
  | .cons head tail =>
    obtain ⟨size_head, head⟩ := StatementExecutes.has_size head
    obtain ⟨size_tail, tail⟩ := FunctionStatementsExecute.has_size tail
    exact ⟨_, .cons head tail⟩
  | .terminal head terminal =>
    obtain ⟨size_head, head⟩ := StatementExecutes.has_size head
    exact ⟨_, .terminal head terminal⟩
termination_by structural trace

theorem ForItemExecutes.has_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : ForItemForm} {a6 : Context} {a7 : Dynamic.Environment} {a8 : Heap}
    (trace : Dynamic.ForItemExecutes program a0 a1 a2 a3 a4 a5 a6 a7 a8) : ∃ size, ForItemExecutes program size a0 a1 a2 a3 a4 a5 a6 a7 a8 := by
  match trace with
  | .letUninitialized monomorphic extension allocate =>
    exact ⟨_, .letUninitialized monomorphic extension allocate⟩
  | .letInitialized evaluate monomorphic extension allocate =>
    obtain ⟨size_evaluate, evaluate⟩ := ExpressionEvaluates.has_size evaluate
    exact ⟨_, .letInitialized evaluate monomorphic extension allocate⟩
  | .letInitializedGeneralized captures polymorphic extension allocate =>
    exact ⟨_, .letInitializedGeneralized captures polymorphic extension allocate⟩
  | .expression evaluate =>
    obtain ⟨size_evaluate, evaluate⟩ := ExpressionEvaluates.has_size evaluate
    exact ⟨_, .expression evaluate⟩
  | .assignValue execute =>
    obtain ⟨size_execute, execute⟩ := SourcePlaceAssignment.has_size execute
    exact ⟨_, .assignValue execute⟩
  | .assignBitNot execute =>
    obtain ⟨size_execute, execute⟩ := SourcePlaceSnapshotUpdate.has_size execute
    exact ⟨_, .assignBitNot execute⟩
termination_by structural trace

theorem ForItemsExecute.has_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : List ForItemForm} {a6 : Context} {a7 : Dynamic.Environment} {a8 : Heap}
    (trace : Dynamic.ForItemsExecute program a0 a1 a2 a3 a4 a5 a6 a7 a8) : ∃ size, ForItemsExecute program size a0 a1 a2 a3 a4 a5 a6 a7 a8 := by
  match trace with
  | .nil  =>
    exact ⟨_, .nil ⟩
  | .cons head tail =>
    obtain ⟨size_head, head⟩ := ForItemExecutes.has_size head
    obtain ⟨size_tail, tail⟩ := ForItemsExecute.has_size tail
    exact ⟨_, .cons head tail⟩
termination_by structural trace

theorem WhileExecutes.has_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : ExpressionId} {a6 : List StatementId} {a7 : Context} {a8 : ControlOutcome} {a9 : Heap}
    (trace : Dynamic.WhileExecutes program a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) : ∃ size, WhileExecutes program size a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 := by
  match trace with
  | .done condition_evaluates =>
    obtain ⟨size_condition_evaluates, condition_evaluates⟩ := ExpressionEvaluates.has_size condition_evaluates
    exact ⟨_, .done condition_evaluates⟩
  | .nextFallthrough condition_evaluates body_executes next =>
    obtain ⟨size_condition_evaluates, condition_evaluates⟩ := ExpressionEvaluates.has_size condition_evaluates
    obtain ⟨size_body_executes, body_executes⟩ := StatementsExecute.has_size body_executes
    obtain ⟨size_next, next⟩ := WhileExecutes.has_size next
    exact ⟨_, .nextFallthrough condition_evaluates body_executes next⟩
  | .nextContinue condition_evaluates body_executes next =>
    obtain ⟨size_condition_evaluates, condition_evaluates⟩ := ExpressionEvaluates.has_size condition_evaluates
    obtain ⟨size_body_executes, body_executes⟩ := StatementsExecute.has_size body_executes
    obtain ⟨size_next, next⟩ := WhileExecutes.has_size next
    exact ⟨_, .nextContinue condition_evaluates body_executes next⟩
  | .breaks condition_evaluates body_executes =>
    obtain ⟨size_condition_evaluates, condition_evaluates⟩ := ExpressionEvaluates.has_size condition_evaluates
    obtain ⟨size_body_executes, body_executes⟩ := StatementsExecute.has_size body_executes
    exact ⟨_, .breaks condition_evaluates body_executes⟩
  | .returns condition_evaluates body_executes =>
    obtain ⟨size_condition_evaluates, condition_evaluates⟩ := ExpressionEvaluates.has_size condition_evaluates
    obtain ⟨size_body_executes, body_executes⟩ := StatementsExecute.has_size body_executes
    exact ⟨_, .returns condition_evaluates body_executes⟩
termination_by structural trace

theorem ForLoopExecutes.has_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : ExpressionId} {a6 : List ForItemForm} {a7 : List StatementId} {a8 : Context} {a9 : ControlOutcome} {a10 : Heap}
    (trace : Dynamic.ForLoopExecutes program a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10) : ∃ size, ForLoopExecutes program size a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 := by
  match trace with
  | .done condition_evaluates =>
    obtain ⟨size_condition_evaluates, condition_evaluates⟩ := ExpressionEvaluates.has_size condition_evaluates
    exact ⟨_, .done condition_evaluates⟩
  | .nextFallthrough condition_evaluates body_executes post_executes next =>
    obtain ⟨size_condition_evaluates, condition_evaluates⟩ := ExpressionEvaluates.has_size condition_evaluates
    obtain ⟨size_body_executes, body_executes⟩ := StatementsExecute.has_size body_executes
    obtain ⟨size_post_executes, post_executes⟩ := ForItemsExecute.has_size post_executes
    obtain ⟨size_next, next⟩ := ForLoopExecutes.has_size next
    exact ⟨_, .nextFallthrough condition_evaluates body_executes post_executes next⟩
  | .nextContinue condition_evaluates body_executes post_executes next =>
    obtain ⟨size_condition_evaluates, condition_evaluates⟩ := ExpressionEvaluates.has_size condition_evaluates
    obtain ⟨size_body_executes, body_executes⟩ := StatementsExecute.has_size body_executes
    obtain ⟨size_post_executes, post_executes⟩ := ForItemsExecute.has_size post_executes
    obtain ⟨size_next, next⟩ := ForLoopExecutes.has_size next
    exact ⟨_, .nextContinue condition_evaluates body_executes post_executes next⟩
  | .breaks condition_evaluates body_executes =>
    obtain ⟨size_condition_evaluates, condition_evaluates⟩ := ExpressionEvaluates.has_size condition_evaluates
    obtain ⟨size_body_executes, body_executes⟩ := StatementsExecute.has_size body_executes
    exact ⟨_, .breaks condition_evaluates body_executes⟩
  | .returns condition_evaluates body_executes =>
    obtain ⟨size_condition_evaluates, condition_evaluates⟩ := ExpressionEvaluates.has_size condition_evaluates
    obtain ⟨size_body_executes, body_executes⟩ := StatementsExecute.has_size body_executes
    exact ⟨_, .returns condition_evaluates body_executes⟩
termination_by structural trace

end

theorem ExpressionEvaluates.positive {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : ExpressionId} {a6 : Value} {a7 : Heap}
    (trace : ExpressionEvaluates program size a0 a1 a2 a3 a4 a5 a6 a7) : 0 < size := by
  cases trace <;> exact stepSize_positive _

theorem ExpressionEvaluates.iff_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : ExpressionId} {a6 : Value} {a7 : Heap} :
    Dynamic.ExpressionEvaluates program a0 a1 a2 a3 a4 a5 a6 a7 ↔ ∃ size, ExpressionEvaluates program size a0 a1 a2 a3 a4 a5 a6 a7 :=
  ⟨ExpressionEvaluates.has_size, fun ⟨_, sized⟩ => sized.sound⟩

theorem ExpressionEvaluates.children_below {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : ExpressionId} {a6 : Value} {a7 : Heap}
    (trace : ExpressionEvaluates program size a0 a1 a2 a3 a4 a5 a6 a7) :
    ∃ children : List Nat, size = stepSize children ∧ ∀ child ∈ children, child < size := by
  cases trace with
  | @intro size_form size_coercions _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_form, size_coercions], rfl, fun _ member => child_lt_stepSize member⟩
  | @generalizedLocal size_coercions _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_coercions], rfl, fun _ member => child_lt_stepSize member⟩

theorem ExpressionFormEvaluates.positive {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : ExpressionForm} {a6 : List RequirementId} {a7 : List CoercionStep} {a8 : Value} {a9 : Heap}
    (trace : ExpressionFormEvaluates program size a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) : 0 < size := by
  cases trace <;> exact stepSize_positive _

theorem ExpressionFormEvaluates.iff_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : ExpressionForm} {a6 : List RequirementId} {a7 : List CoercionStep} {a8 : Value} {a9 : Heap} :
    Dynamic.ExpressionFormEvaluates program a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 ↔ ∃ size, ExpressionFormEvaluates program size a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 :=
  ⟨ExpressionFormEvaluates.has_size, fun ⟨_, sized⟩ => sized.sound⟩

theorem ExpressionFormEvaluates.children_below {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : ExpressionForm} {a6 : List RequirementId} {a7 : List CoercionStep} {a8 : Value} {a9 : Heap}
    (trace : ExpressionFormEvaluates program size a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) :
    ∃ children : List Nat, size = stepSize children ∧ ∀ child ∈ children, child < size := by
  cases trace with
  | @literal _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[], rfl, fun _ member => child_lt_stepSize member⟩
  | @integerLiteral _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[], rfl, fun _ member => child_lt_stepSize member⟩
  | @«local» _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[], rfl, fun _ member => child_lt_stepSize member⟩
  | @localEmptyMapping _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[], rfl, fun _ member => child_lt_stepSize member⟩
  | @declaration _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[], rfl, fun _ member => child_lt_stepSize member⟩
  | @builtinFunction _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[], rfl, fun _ member => child_lt_stepSize member⟩
  | @builtinBoolean _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[], rfl, fun _ member => child_lt_stepSize member⟩
  | @group size_inner_evaluates _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_inner_evaluates], rfl, fun _ member => child_lt_stepSize member⟩
  | @tuple size_elements_evaluate _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_elements_evaluate], rfl, fun _ member => child_lt_stepSize member⟩
  | @unary size_operand_evaluates size_applies _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_operand_evaluates, size_applies], rfl, fun _ member => child_lt_stepSize member⟩
  | @binaryShortCircuit size_left_evaluates _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_left_evaluates], rfl, fun _ member => child_lt_stepSize member⟩
  | @binaryEvaluateRight size_left_evaluates size_right_evaluates size_applies _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_left_evaluates, size_right_evaluates, size_applies], rfl, fun _ member => child_lt_stepSize member⟩
  | @conditionalTrue size_condition_evaluates size_branch_evaluates _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_condition_evaluates, size_branch_evaluates], rfl, fun _ member => child_lt_stepSize member⟩
  | @conditionalFalse size_condition_evaluates size_branch_evaluates _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_condition_evaluates, size_branch_evaluates], rfl, fun _ member => child_lt_stepSize member⟩
  | @lambda _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[], rfl, fun _ member => child_lt_stepSize member⟩
  | @directCall size_arguments_evaluate size_applies _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_arguments_evaluate, size_applies], rfl, fun _ member => child_lt_stepSize member⟩
  | @builtinCall size_arguments_evaluate size_applies _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_arguments_evaluate, size_applies], rfl, fun _ member => child_lt_stepSize member⟩
  | @indirectCall size_callee_evaluates size_arguments_evaluate size_argument_coercions size_applies _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_callee_evaluates, size_arguments_evaluate, size_argument_coercions, size_applies], rfl, fun _ member => child_lt_stepSize member⟩
  | @constructor size_arguments_evaluate _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_arguments_evaluate], rfl, fun _ member => child_lt_stepSize member⟩
  | @member size_base_evaluates _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_base_evaluates], rfl, fun _ member => child_lt_stepSize member⟩
  | @proxy _ _ _ _ _ _ _ _ _ =>
    exact ⟨[], rfl, fun _ member => child_lt_stepSize member⟩
  | @indexFound size_base_evaluates size_index_evaluates _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_base_evaluates, size_index_evaluates], rfl, fun _ member => child_lt_stepSize member⟩
  | @indexDefault size_base_evaluates size_index_evaluates _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_base_evaluates, size_index_evaluates], rfl, fun _ member => child_lt_stepSize member⟩

theorem ExpressionsEvaluate.positive {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : List ExpressionId} {a6 : List Value} {a7 : Heap}
    (trace : ExpressionsEvaluate program size a0 a1 a2 a3 a4 a5 a6 a7) : 0 < size := by
  cases trace <;> exact stepSize_positive _

theorem ExpressionsEvaluate.iff_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : List ExpressionId} {a6 : List Value} {a7 : Heap} :
    Dynamic.ExpressionsEvaluate program a0 a1 a2 a3 a4 a5 a6 a7 ↔ ∃ size, ExpressionsEvaluate program size a0 a1 a2 a3 a4 a5 a6 a7 :=
  ⟨ExpressionsEvaluate.has_size, fun ⟨_, sized⟩ => sized.sound⟩

theorem ExpressionsEvaluate.children_below {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : List ExpressionId} {a6 : List Value} {a7 : Heap}
    (trace : ExpressionsEvaluate program size a0 a1 a2 a3 a4 a5 a6 a7) :
    ∃ children : List Nat, size = stepSize children ∧ ∀ child ∈ children, child < size := by
  cases trace with
  | @nil _ _ _ _ _ =>
    exact ⟨[], rfl, fun _ member => child_lt_stepSize member⟩
  | @cons size_head size_tail _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_head, size_tail], rfl, fun _ member => child_lt_stepSize member⟩

theorem SourceProjectionsEvaluate.positive {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : List PlaceProjection} {a6 : List EvaluatedProjection} {a7 : Heap}
    (trace : SourceProjectionsEvaluate program size a0 a1 a2 a3 a4 a5 a6 a7) : 0 < size := by
  cases trace <;> exact stepSize_positive _

theorem SourceProjectionsEvaluate.iff_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : List PlaceProjection} {a6 : List EvaluatedProjection} {a7 : Heap} :
    Dynamic.SourceProjectionsEvaluate program a0 a1 a2 a3 a4 a5 a6 a7 ↔ ∃ size, SourceProjectionsEvaluate program size a0 a1 a2 a3 a4 a5 a6 a7 :=
  ⟨SourceProjectionsEvaluate.has_size, fun ⟨_, sized⟩ => sized.sound⟩

theorem SourceProjectionsEvaluate.children_below {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : List PlaceProjection} {a6 : List EvaluatedProjection} {a7 : Heap}
    (trace : SourceProjectionsEvaluate program size a0 a1 a2 a3 a4 a5 a6 a7) :
    ∃ children : List Nat, size = stepSize children ∧ ∀ child ∈ children, child < size := by
  cases trace with
  | @nil _ _ _ _ _ =>
    exact ⟨[], rfl, fun _ member => child_lt_stepSize member⟩
  | @member size_tail _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_tail], rfl, fun _ member => child_lt_stepSize member⟩
  | @index size_head size_tail _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_head, size_tail], rfl, fun _ member => child_lt_stepSize member⟩

theorem SourcePlaceResolves.positive {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : PlaceResolution} {a6 : ResolvedPlace} {a7 : Heap}
    (trace : SourcePlaceResolves program size a0 a1 a2 a3 a4 a5 a6 a7) : 0 < size := by
  cases trace <;> exact stepSize_positive _

theorem SourcePlaceResolves.iff_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : PlaceResolution} {a6 : ResolvedPlace} {a7 : Heap} :
    Dynamic.SourcePlaceResolves program a0 a1 a2 a3 a4 a5 a6 a7 ↔ ∃ size, SourcePlaceResolves program size a0 a1 a2 a3 a4 a5 a6 a7 :=
  ⟨SourcePlaceResolves.has_size, fun ⟨_, sized⟩ => sized.sound⟩

theorem SourcePlaceResolves.children_below {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : PlaceResolution} {a6 : ResolvedPlace} {a7 : Heap}
    (trace : SourcePlaceResolves program size a0 a1 a2 a3 a4 a5 a6 a7) :
    ∃ children : List Nat, size = stepSize children ∧ ∀ child ∈ children, child < size := by
  cases trace with
  | @intro size_evaluate _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_evaluate], rfl, fun _ member => child_lt_stepSize member⟩

theorem SourcePlaceAssignment.positive {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : (Option Value → Value → Value → Prop)} {a4 : Dynamic.Environment} {a5 : Heap} {a6 : PlaceResolution} {a7 : ExpressionId} {a8 : Value} {a9 : Heap}
    (trace : SourcePlaceAssignment program size a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) : 0 < size := by
  cases trace <;> exact stepSize_positive _

theorem SourcePlaceAssignment.iff_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : (Option Value → Value → Value → Prop)} {a4 : Dynamic.Environment} {a5 : Heap} {a6 : PlaceResolution} {a7 : ExpressionId} {a8 : Value} {a9 : Heap} :
    Dynamic.SourcePlaceAssignment program a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 ↔ ∃ size, SourcePlaceAssignment program size a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 :=
  ⟨SourcePlaceAssignment.has_size, fun ⟨_, sized⟩ => sized.sound⟩

theorem SourcePlaceAssignment.children_below {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : (Option Value → Value → Value → Prop)} {a4 : Dynamic.Environment} {a5 : Heap} {a6 : PlaceResolution} {a7 : ExpressionId} {a8 : Value} {a9 : Heap}
    (trace : SourcePlaceAssignment program size a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) :
    ∃ children : List Nat, size = stepSize children ∧ ∀ child ∈ children, child < size := by
  cases trace with
  | @intro size_resolve size_evaluate_right _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_resolve, size_evaluate_right], rfl, fun _ member => child_lt_stepSize member⟩

theorem SourcePlaceSnapshotUpdate.positive {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : (Option Value → Value → Prop)} {a4 : Dynamic.Environment} {a5 : Heap} {a6 : PlaceResolution} {a7 : Value} {a8 : Heap}
    (trace : SourcePlaceSnapshotUpdate program size a0 a1 a2 a3 a4 a5 a6 a7 a8) : 0 < size := by
  cases trace <;> exact stepSize_positive _

theorem SourcePlaceSnapshotUpdate.iff_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : (Option Value → Value → Prop)} {a4 : Dynamic.Environment} {a5 : Heap} {a6 : PlaceResolution} {a7 : Value} {a8 : Heap} :
    Dynamic.SourcePlaceSnapshotUpdate program a0 a1 a2 a3 a4 a5 a6 a7 a8 ↔ ∃ size, SourcePlaceSnapshotUpdate program size a0 a1 a2 a3 a4 a5 a6 a7 a8 :=
  ⟨SourcePlaceSnapshotUpdate.has_size, fun ⟨_, sized⟩ => sized.sound⟩

theorem SourcePlaceSnapshotUpdate.children_below {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : (Option Value → Value → Prop)} {a4 : Dynamic.Environment} {a5 : Heap} {a6 : PlaceResolution} {a7 : Value} {a8 : Heap}
    (trace : SourcePlaceSnapshotUpdate program size a0 a1 a2 a3 a4 a5 a6 a7 a8) :
    ∃ children : List Nat, size = stepSize children ∧ ∀ child ∈ children, child < size := by
  cases trace with
  | @intro size_resolve _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_resolve], rfl, fun _ member => child_lt_stepSize member⟩

theorem UnaryOperationApplies.positive {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : Heap} {a3 : Syntax.UnaryOp} {a4 : List RequirementId} {a5 : Value} {a6 : Value} {a7 : Heap}
    (trace : UnaryOperationApplies program size a0 a1 a2 a3 a4 a5 a6 a7) : 0 < size := by
  cases trace <;> exact stepSize_positive _

theorem UnaryOperationApplies.iff_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : Heap} {a3 : Syntax.UnaryOp} {a4 : List RequirementId} {a5 : Value} {a6 : Value} {a7 : Heap} :
    Dynamic.UnaryOperationApplies program a0 a1 a2 a3 a4 a5 a6 a7 ↔ ∃ size, UnaryOperationApplies program size a0 a1 a2 a3 a4 a5 a6 a7 :=
  ⟨UnaryOperationApplies.has_size, fun ⟨_, sized⟩ => sized.sound⟩

theorem UnaryOperationApplies.children_below {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : Heap} {a3 : Syntax.UnaryOp} {a4 : List RequirementId} {a5 : Value} {a6 : Value} {a7 : Heap}
    (trace : UnaryOperationApplies program size a0 a1 a2 a3 a4 a5 a6 a7) :
    ∃ children : List Nat, size = stepSize children ∧ ∀ child ∈ children, child < size := by
  cases trace with
  | @primitive _ _ _ _ _ _ _ =>
    exact ⟨[], rfl, fun _ member => child_lt_stepSize member⟩
  | @method size_invokes _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_invokes], rfl, fun _ member => child_lt_stepSize member⟩

theorem BinaryOperationApplies.positive {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : Heap} {a3 : Syntax.BinaryOp} {a4 : List RequirementId} {a5 : Value} {a6 : Value} {a7 : Value} {a8 : Heap}
    (trace : BinaryOperationApplies program size a0 a1 a2 a3 a4 a5 a6 a7 a8) : 0 < size := by
  cases trace <;> exact stepSize_positive _

theorem BinaryOperationApplies.iff_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : Heap} {a3 : Syntax.BinaryOp} {a4 : List RequirementId} {a5 : Value} {a6 : Value} {a7 : Value} {a8 : Heap} :
    Dynamic.BinaryOperationApplies program a0 a1 a2 a3 a4 a5 a6 a7 a8 ↔ ∃ size, BinaryOperationApplies program size a0 a1 a2 a3 a4 a5 a6 a7 a8 :=
  ⟨BinaryOperationApplies.has_size, fun ⟨_, sized⟩ => sized.sound⟩

theorem BinaryOperationApplies.children_below {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : Heap} {a3 : Syntax.BinaryOp} {a4 : List RequirementId} {a5 : Value} {a6 : Value} {a7 : Value} {a8 : Heap}
    (trace : BinaryOperationApplies program size a0 a1 a2 a3 a4 a5 a6 a7 a8) :
    ∃ children : List Nat, size = stepSize children ∧ ∀ child ∈ children, child < size := by
  cases trace with
  | @primitive _ _ _ _ _ _ _ _ =>
    exact ⟨[], rfl, fun _ member => child_lt_stepSize member⟩
  | @method size_invokes _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_invokes], rfl, fun _ member => child_lt_stepSize member⟩

theorem CoercionStepExecutes.positive {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : Heap} {a3 : CoercionStep} {a4 : Value} {a5 : Value} {a6 : Heap}
    (trace : CoercionStepExecutes program size a0 a1 a2 a3 a4 a5 a6) : 0 < size := by
  cases trace <;> exact stepSize_positive _

theorem CoercionStepExecutes.iff_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : Heap} {a3 : CoercionStep} {a4 : Value} {a5 : Value} {a6 : Heap} :
    Dynamic.CoercionStepExecutes program a0 a1 a2 a3 a4 a5 a6 ↔ ∃ size, CoercionStepExecutes program size a0 a1 a2 a3 a4 a5 a6 :=
  ⟨CoercionStepExecutes.has_size, fun ⟨_, sized⟩ => sized.sound⟩

theorem CoercionStepExecutes.children_below {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : Heap} {a3 : CoercionStep} {a4 : Value} {a5 : Value} {a6 : Heap}
    (trace : CoercionStepExecutes program size a0 a1 a2 a3 a4 a5 a6) :
    ∃ children : List Nat, size = stepSize children ∧ ∀ child ∈ children, child < size := by
  cases trace with
  | @primitive _ _ _ _ _ _ _ _ =>
    exact ⟨[], rfl, fun _ member => child_lt_stepSize member⟩
  | @method size_invokes _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_invokes], rfl, fun _ member => child_lt_stepSize member⟩

theorem CoercionPathExecutes.positive {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : Heap} {a3 : List CoercionStep} {a4 : Value} {a5 : Value} {a6 : Heap}
    (trace : CoercionPathExecutes program size a0 a1 a2 a3 a4 a5 a6) : 0 < size := by
  cases trace <;> exact stepSize_positive _

theorem CoercionPathExecutes.iff_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : Heap} {a3 : List CoercionStep} {a4 : Value} {a5 : Value} {a6 : Heap} :
    Dynamic.CoercionPathExecutes program a0 a1 a2 a3 a4 a5 a6 ↔ ∃ size, CoercionPathExecutes program size a0 a1 a2 a3 a4 a5 a6 :=
  ⟨CoercionPathExecutes.has_size, fun ⟨_, sized⟩ => sized.sound⟩

theorem CoercionPathExecutes.children_below {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : Heap} {a3 : List CoercionStep} {a4 : Value} {a5 : Value} {a6 : Heap}
    (trace : CoercionPathExecutes program size a0 a1 a2 a3 a4 a5 a6) :
    ∃ children : List Nat, size = stepSize children ∧ ∀ child ∈ children, child < size := by
  cases trace with
  | @nil _ _ _ _ =>
    exact ⟨[], rfl, fun _ member => child_lt_stepSize member⟩
  | @cons size_head size_tail _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_head, size_tail], rfl, fun _ member => child_lt_stepSize member⟩

theorem CallableApplies.positive {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : EvidenceEnvironment} {a3 : Heap} {a4 : Value} {a5 : List Value} {a6 : Value} {a7 : Heap}
    (trace : CallableApplies program size a0 a1 a2 a3 a4 a5 a6 a7) : 0 < size := by
  cases trace <;> exact stepSize_positive _

theorem CallableApplies.iff_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : EvidenceEnvironment} {a3 : Heap} {a4 : Value} {a5 : List Value} {a6 : Value} {a7 : Heap} :
    Dynamic.CallableApplies program a0 a1 a2 a3 a4 a5 a6 a7 ↔ ∃ size, CallableApplies program size a0 a1 a2 a3 a4 a5 a6 a7 :=
  ⟨CallableApplies.has_size, fun ⟨_, sized⟩ => sized.sound⟩

theorem CallableApplies.children_below {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : EvidenceEnvironment} {a3 : Heap} {a4 : Value} {a5 : List Value} {a6 : Value} {a7 : Heap}
    (trace : CallableApplies program size a0 a1 a2 a3 a4 a5 a6 a7) :
    ∃ children : List Nat, size = stepSize children ∧ ∀ child ∈ children, child < size := by
  cases trace with
  | @builtin _ _ _ _ _ _ _ _ =>
    exact ⟨[], rfl, fun _ member => child_lt_stepSize member⟩
  | @global size_invokes _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_invokes], rfl, fun _ member => child_lt_stepSize member⟩
  | @closure size_execute _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_execute], rfl, fun _ member => child_lt_stepSize member⟩
  | @closureUnit size_execute _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_execute], rfl, fun _ member => child_lt_stepSize member⟩

theorem BodyInvokes.positive {program : Program} {size : Nat} {a0 : BodyInstance} {a1 : EvidenceEnvironment} {a2 : Heap} {a3 : List Value} {a4 : Value} {a5 : Heap}
    (trace : BodyInvokes program size a0 a1 a2 a3 a4 a5) : 0 < size := by
  cases trace <;> exact stepSize_positive _

theorem BodyInvokes.iff_size {program : Program} {a0 : BodyInstance} {a1 : EvidenceEnvironment} {a2 : Heap} {a3 : List Value} {a4 : Value} {a5 : Heap} :
    Dynamic.BodyInvokes program a0 a1 a2 a3 a4 a5 ↔ ∃ size, BodyInvokes program size a0 a1 a2 a3 a4 a5 :=
  ⟨BodyInvokes.has_size, fun ⟨_, sized⟩ => sized.sound⟩

theorem BodyInvokes.children_below {program : Program} {size : Nat} {a0 : BodyInstance} {a1 : EvidenceEnvironment} {a2 : Heap} {a3 : List Value} {a4 : Value} {a5 : Heap}
    (trace : BodyInvokes program size a0 a1 a2 a3 a4 a5) :
    ∃ children : List Nat, size = stepSize children ∧ ∀ child ∈ children, child < size := by
  cases trace with
  | @returned size_execute _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_execute], rfl, fun _ member => child_lt_stepSize member⟩
  | @unit size_execute _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_execute], rfl, fun _ member => child_lt_stepSize member⟩

theorem StatementExecutes.positive {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : StatementId} {a6 : Context} {a7 : ControlOutcome} {a8 : Heap}
    (trace : StatementExecutes program size a0 a1 a2 a3 a4 a5 a6 a7 a8) : 0 < size := by
  cases trace <;> exact stepSize_positive _

theorem StatementExecutes.iff_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : StatementId} {a6 : Context} {a7 : ControlOutcome} {a8 : Heap} :
    Dynamic.StatementExecutes program a0 a1 a2 a3 a4 a5 a6 a7 a8 ↔ ∃ size, StatementExecutes program size a0 a1 a2 a3 a4 a5 a6 a7 a8 :=
  ⟨StatementExecutes.has_size, fun ⟨_, sized⟩ => sized.sound⟩

theorem StatementExecutes.children_below {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : StatementId} {a6 : Context} {a7 : ControlOutcome} {a8 : Heap}
    (trace : StatementExecutes program size a0 a1 a2 a3 a4 a5 a6 a7 a8) :
    ∃ children : List Nat, size = stepSize children ∧ ∀ child ∈ children, child < size := by
  cases trace with
  | @letUninitialized _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[], rfl, fun _ member => child_lt_stepSize member⟩
  | @letInitialized size_evaluate _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_evaluate], rfl, fun _ member => child_lt_stepSize member⟩
  | @letInitializedGeneralized _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[], rfl, fun _ member => child_lt_stepSize member⟩
  | @returnUnit _ _ _ _ _ _ _ _ _ =>
    exact ⟨[], rfl, fun _ member => child_lt_stepSize member⟩
  | @returnValue size_evaluate _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_evaluate], rfl, fun _ member => child_lt_stepSize member⟩
  | @expression size_evaluate _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_evaluate], rfl, fun _ member => child_lt_stepSize member⟩
  | @assignValue size_assignment_executes _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_assignment_executes], rfl, fun _ member => child_lt_stepSize member⟩
  | @assignBitNot size_assignment_executes _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_assignment_executes], rfl, fun _ member => child_lt_stepSize member⟩
  | @ifTrue size_condition_evaluates size_body_executes _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_condition_evaluates, size_body_executes], rfl, fun _ member => child_lt_stepSize member⟩
  | @ifFalseWithoutElse size_condition_evaluates _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_condition_evaluates], rfl, fun _ member => child_lt_stepSize member⟩
  | @ifFalseWithElse size_condition_evaluates size_body_executes _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_condition_evaluates, size_body_executes], rfl, fun _ member => child_lt_stepSize member⟩
  | @block size_body_executes _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_body_executes], rfl, fun _ member => child_lt_stepSize member⟩
  | @matchArm size_scrutinee_evaluates size_execute _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_scrutinee_evaluates, size_execute], rfl, fun _ member => child_lt_stepSize member⟩
  | @matchDefault size_scrutinee_evaluates size_execute _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_scrutinee_evaluates, size_execute], rfl, fun _ member => child_lt_stepSize member⟩
  | @matchNoBranch size_scrutinee_evaluates _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_scrutinee_evaluates], rfl, fun _ member => child_lt_stepSize member⟩
  | @forLoop size_initializer_executes size_iterate _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_initializer_executes, size_iterate], rfl, fun _ member => child_lt_stepSize member⟩
  | @whileLoop size_iterate _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_iterate], rfl, fun _ member => child_lt_stepSize member⟩
  | @breakStmt _ _ _ _ _ _ _ _ _ =>
    exact ⟨[], rfl, fun _ member => child_lt_stepSize member⟩
  | @continueStmt _ _ _ _ _ _ _ _ _ =>
    exact ⟨[], rfl, fun _ member => child_lt_stepSize member⟩

theorem StatementsExecute.positive {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : List StatementId} {a6 : Context} {a7 : ControlOutcome} {a8 : Heap}
    (trace : StatementsExecute program size a0 a1 a2 a3 a4 a5 a6 a7 a8) : 0 < size := by
  cases trace <;> exact stepSize_positive _

theorem StatementsExecute.iff_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : List StatementId} {a6 : Context} {a7 : ControlOutcome} {a8 : Heap} :
    Dynamic.StatementsExecute program a0 a1 a2 a3 a4 a5 a6 a7 a8 ↔ ∃ size, StatementsExecute program size a0 a1 a2 a3 a4 a5 a6 a7 a8 :=
  ⟨StatementsExecute.has_size, fun ⟨_, sized⟩ => sized.sound⟩

theorem StatementsExecute.children_below {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : List StatementId} {a6 : Context} {a7 : ControlOutcome} {a8 : Heap}
    (trace : StatementsExecute program size a0 a1 a2 a3 a4 a5 a6 a7 a8) :
    ∃ children : List Nat, size = stepSize children ∧ ∀ child ∈ children, child < size := by
  cases trace with
  | @nil _ _ _ _ _ =>
    exact ⟨[], rfl, fun _ member => child_lt_stepSize member⟩
  | @cons size_head size_tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_head, size_tail], rfl, fun _ member => child_lt_stepSize member⟩
  | @terminal size_head _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_head], rfl, fun _ member => child_lt_stepSize member⟩

theorem FunctionStatementsExecute.positive {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : List StatementId} {a6 : Context} {a7 : ControlOutcome} {a8 : Heap}
    (trace : FunctionStatementsExecute program size a0 a1 a2 a3 a4 a5 a6 a7 a8) : 0 < size := by
  cases trace <;> exact stepSize_positive _

theorem FunctionStatementsExecute.iff_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : List StatementId} {a6 : Context} {a7 : ControlOutcome} {a8 : Heap} :
    Dynamic.FunctionStatementsExecute program a0 a1 a2 a3 a4 a5 a6 a7 a8 ↔ ∃ size, FunctionStatementsExecute program size a0 a1 a2 a3 a4 a5 a6 a7 a8 :=
  ⟨FunctionStatementsExecute.has_size, fun ⟨_, sized⟩ => sized.sound⟩

theorem FunctionStatementsExecute.children_below {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : List StatementId} {a6 : Context} {a7 : ControlOutcome} {a8 : Heap}
    (trace : FunctionStatementsExecute program size a0 a1 a2 a3 a4 a5 a6 a7 a8) :
    ∃ children : List Nat, size = stepSize children ∧ ∀ child ∈ children, child < size := by
  cases trace with
  | @nil _ _ _ _ _ =>
    exact ⟨[], rfl, fun _ member => child_lt_stepSize member⟩
  | @tailExpression size_evaluate _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_evaluate], rfl, fun _ member => child_lt_stepSize member⟩
  | @singleton size_execute _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_execute], rfl, fun _ member => child_lt_stepSize member⟩
  | @cons size_head size_tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_head, size_tail], rfl, fun _ member => child_lt_stepSize member⟩
  | @terminal size_head _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_head], rfl, fun _ member => child_lt_stepSize member⟩

theorem ForItemExecutes.positive {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : ForItemForm} {a6 : Context} {a7 : Dynamic.Environment} {a8 : Heap}
    (trace : ForItemExecutes program size a0 a1 a2 a3 a4 a5 a6 a7 a8) : 0 < size := by
  cases trace <;> exact stepSize_positive _

theorem ForItemExecutes.iff_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : ForItemForm} {a6 : Context} {a7 : Dynamic.Environment} {a8 : Heap} :
    Dynamic.ForItemExecutes program a0 a1 a2 a3 a4 a5 a6 a7 a8 ↔ ∃ size, ForItemExecutes program size a0 a1 a2 a3 a4 a5 a6 a7 a8 :=
  ⟨ForItemExecutes.has_size, fun ⟨_, sized⟩ => sized.sound⟩

theorem ForItemExecutes.children_below {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : ForItemForm} {a6 : Context} {a7 : Dynamic.Environment} {a8 : Heap}
    (trace : ForItemExecutes program size a0 a1 a2 a3 a4 a5 a6 a7 a8) :
    ∃ children : List Nat, size = stepSize children ∧ ∀ child ∈ children, child < size := by
  cases trace with
  | @letUninitialized _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[], rfl, fun _ member => child_lt_stepSize member⟩
  | @letInitialized size_evaluate _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_evaluate], rfl, fun _ member => child_lt_stepSize member⟩
  | @letInitializedGeneralized _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[], rfl, fun _ member => child_lt_stepSize member⟩
  | @expression size_evaluate _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_evaluate], rfl, fun _ member => child_lt_stepSize member⟩
  | @assignValue size_execute _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_execute], rfl, fun _ member => child_lt_stepSize member⟩
  | @assignBitNot size_execute _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_execute], rfl, fun _ member => child_lt_stepSize member⟩

theorem ForItemsExecute.positive {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : List ForItemForm} {a6 : Context} {a7 : Dynamic.Environment} {a8 : Heap}
    (trace : ForItemsExecute program size a0 a1 a2 a3 a4 a5 a6 a7 a8) : 0 < size := by
  cases trace <;> exact stepSize_positive _

theorem ForItemsExecute.iff_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : List ForItemForm} {a6 : Context} {a7 : Dynamic.Environment} {a8 : Heap} :
    Dynamic.ForItemsExecute program a0 a1 a2 a3 a4 a5 a6 a7 a8 ↔ ∃ size, ForItemsExecute program size a0 a1 a2 a3 a4 a5 a6 a7 a8 :=
  ⟨ForItemsExecute.has_size, fun ⟨_, sized⟩ => sized.sound⟩

theorem ForItemsExecute.children_below {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : List ForItemForm} {a6 : Context} {a7 : Dynamic.Environment} {a8 : Heap}
    (trace : ForItemsExecute program size a0 a1 a2 a3 a4 a5 a6 a7 a8) :
    ∃ children : List Nat, size = stepSize children ∧ ∀ child ∈ children, child < size := by
  cases trace with
  | @nil _ _ _ _ _ =>
    exact ⟨[], rfl, fun _ member => child_lt_stepSize member⟩
  | @cons size_head size_tail _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_head, size_tail], rfl, fun _ member => child_lt_stepSize member⟩

theorem WhileExecutes.positive {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : ExpressionId} {a6 : List StatementId} {a7 : Context} {a8 : ControlOutcome} {a9 : Heap}
    (trace : WhileExecutes program size a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) : 0 < size := by
  cases trace <;> exact stepSize_positive _

theorem WhileExecutes.iff_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : ExpressionId} {a6 : List StatementId} {a7 : Context} {a8 : ControlOutcome} {a9 : Heap} :
    Dynamic.WhileExecutes program a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 ↔ ∃ size, WhileExecutes program size a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 :=
  ⟨WhileExecutes.has_size, fun ⟨_, sized⟩ => sized.sound⟩

theorem WhileExecutes.children_below {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : ExpressionId} {a6 : List StatementId} {a7 : Context} {a8 : ControlOutcome} {a9 : Heap}
    (trace : WhileExecutes program size a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) :
    ∃ children : List Nat, size = stepSize children ∧ ∀ child ∈ children, child < size := by
  cases trace with
  | @done size_condition_evaluates _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_condition_evaluates], rfl, fun _ member => child_lt_stepSize member⟩
  | @nextFallthrough size_condition_evaluates size_body_executes size_next _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_condition_evaluates, size_body_executes, size_next], rfl, fun _ member => child_lt_stepSize member⟩
  | @nextContinue size_condition_evaluates size_body_executes size_next _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_condition_evaluates, size_body_executes, size_next], rfl, fun _ member => child_lt_stepSize member⟩
  | @breaks size_condition_evaluates size_body_executes _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_condition_evaluates, size_body_executes], rfl, fun _ member => child_lt_stepSize member⟩
  | @returns size_condition_evaluates size_body_executes _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_condition_evaluates, size_body_executes], rfl, fun _ member => child_lt_stepSize member⟩

theorem ForLoopExecutes.positive {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : ExpressionId} {a6 : List ForItemForm} {a7 : List StatementId} {a8 : Context} {a9 : ControlOutcome} {a10 : Heap}
    (trace : ForLoopExecutes program size a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10) : 0 < size := by
  cases trace <;> exact stepSize_positive _

theorem ForLoopExecutes.iff_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : ExpressionId} {a6 : List ForItemForm} {a7 : List StatementId} {a8 : Context} {a9 : ControlOutcome} {a10 : Heap} :
    Dynamic.ForLoopExecutes program a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 ↔ ∃ size, ForLoopExecutes program size a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 :=
  ⟨ForLoopExecutes.has_size, fun ⟨_, sized⟩ => sized.sound⟩

theorem ForLoopExecutes.children_below {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : ExpressionId} {a6 : List ForItemForm} {a7 : List StatementId} {a8 : Context} {a9 : ControlOutcome} {a10 : Heap}
    (trace : ForLoopExecutes program size a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10) :
    ∃ children : List Nat, size = stepSize children ∧ ∀ child ∈ children, child < size := by
  cases trace with
  | @done size_condition_evaluates _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_condition_evaluates], rfl, fun _ member => child_lt_stepSize member⟩
  | @nextFallthrough size_condition_evaluates size_body_executes size_post_executes size_next _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_condition_evaluates, size_body_executes, size_post_executes, size_next], rfl, fun _ member => child_lt_stepSize member⟩
  | @nextContinue size_condition_evaluates size_body_executes size_post_executes size_next _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_condition_evaluates, size_body_executes, size_post_executes, size_next], rfl, fun _ member => child_lt_stepSize member⟩
  | @breaks size_condition_evaluates size_body_executes _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_condition_evaluates, size_body_executes], rfl, fun _ member => child_lt_stepSize member⟩
  | @returns size_condition_evaluates size_body_executes _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_condition_evaluates, size_body_executes], rfl, fun _ member => child_lt_stepSize member⟩

mutual
  inductive ExpressionFaults (program : Program) : Nat →
      Context → EvidenceEnvironment → TypedSource → Dynamic.Environment →
        Heap → ExpressionId → SemanticFault → Heap → Prop where
    | missing
        {context evidence source environment heap id}
        (absent : ExpressionMissing source id) :
        ExpressionFaults program (stepSize []) context evidence source environment heap id
          (.missingExpression id) heap
    | form
        {size_fault : Nat}
        {context evidence source environment before after id node reason}
        (contains : ContainsExpression source id node)
        (fault : ExpressionFormFaults program size_fault context evidence source environment
          before node.form node.requirements node.coercions reason after) :
        ExpressionFaults program (stepSize [size_fault]) context evidence source environment before id
          reason after
    | coercion
        {size_form size_fault : Nat}
        {context evidence source environment before middle after id node raw reason}
        (contains : ContainsExpression source id node)
        (form : ExpressionFormEvaluates program size_form context evidence source environment
          before node.form node.requirements node.coercions raw middle)
        (fault : CoercionPathFaults program size_fault context evidence middle node.coercions
          raw reason after) :
        ExpressionFaults program (stepSize [size_form, size_fault]) context evidence source environment before id
          reason after
    | generalizedLocalRequirement
        {context evidence source environment heap id node name binder owned
          location cell function substitution failed}
        (contains : ContainsExpression source id node)
        (form_eq : node.form = .reference name (.local binder))
        (layout : OrdinaryRequirementLayout node.requirements node.coercions
          owned)
        (lookup : Dynamic.Environment.LooksUp environment binder location)
        (read : Heap.Reads heap location cell)
        (descriptor : cell.generalized = some function)
        (context_fields : RuntimeContextFields function.definitionContext
          context)
        (selection : LocalSchemeRuntimeSelection context function.binder
          node.rawType owned substitution)
        (fault : RequirementsFault context evidence owned
          (instantiateLocalSchemePredicates substitution function.binder)
          failed) :
        ExpressionFaults program (stepSize []) context evidence source environment heap id
          (.unsatisfiedRequirement failed) heap
    | generalizedLocalCoercion
        {size_fault : Nat}
        {context evidence source environment before after id node name binder
          owned location cell function substitution produced reason}
        (contains : ContainsExpression source id node)
        (form_eq : node.form = .reference name (.local binder))
        (layout : OrdinaryRequirementLayout node.requirements node.coercions
          owned)
        (lookup : Dynamic.Environment.LooksUp environment binder location)
        (read : Heap.Reads before location cell)
        (descriptor : cell.generalized = some function)
        (context_fields : RuntimeContextFields function.definitionContext
          context)
        (instantiation : LocalSchemeRuntimeInstantiation context evidence
          function.binder node.rawType owned substitution produced)
        (fault : CoercionPathFaults program size_fault context evidence before
          node.coercions
          (.closure (function.instantiate substitution
            (produced ++ evidence.applySubstitution substitution)))
          reason after) :
        ExpressionFaults program (stepSize [size_fault]) context evidence source environment before id
          reason after

  inductive ExpressionFormFaults (program : Program) : Nat →
      Context → EvidenceEnvironment → TypedSource → Dynamic.Environment →
        Heap → ExpressionForm → List RequirementId →
        List CoercionStep → SemanticFault → Heap → Prop where
    | integerRequirement
        {context evidence source environment heap literal resolution requirements
          coercions}
        (layout : OrdinaryRequirementLayout requirements coercions
          [resolution.requirement])
        (fault : RequirementUnavailable context evidence resolution.requirement) :
        ExpressionFormFaults program (stepSize []) context evidence source environment heap
          (.integerLiteral literal resolution) requirements coercions
          (.unsatisfiedRequirement resolution.requirement) heap
    | localUnbound
        {context evidence source environment heap name binder requirements coercions
          owned}
        (layout : OrdinaryRequirementLayout requirements coercions owned)
        (unbound : environment.Unbound binder) :
        ExpressionFormFaults program (stepSize []) context evidence source environment heap
          (.reference name (.local binder)) requirements coercions
          (.unboundLocal binder) heap
    | localDangling
        {context evidence source environment heap name binder requirements coercions
          owned location}
        (layout : OrdinaryRequirementLayout requirements coercions owned)
        (lookup : Dynamic.Environment.LooksUp environment binder location)
        (dangling : heap.Dangling location) :
        ExpressionFormFaults program (stepSize []) context evidence source environment heap
          (.reference name (.local binder)) requirements coercions
          (.danglingLocation location) heap
    | localUninitialized
        {context evidence source environment heap name binder requirements coercions
          owned location cell}
        (layout : OrdinaryRequirementLayout requirements coercions owned)
        (lookup : Dynamic.Environment.LooksUp environment binder location)
        (read : Heap.Reads heap location cell)
        (descriptor_empty : cell.generalized = none)
        (empty : cell.value = none)
        (not_mapping : ¬ ∃ keyType valueType, cell.type = .mapping keyType valueType) :
        ExpressionFormFaults program (stepSize []) context evidence source environment heap
          (.reference name (.local binder)) requirements coercions
          (.uninitializedLocation location) heap
    | declarationRequirement
        {context evidence source environment heap name instantiation requirements
          coercions owned failed}
        (layout : OrdinaryRequirementLayout requirements coercions owned)
        (fault : RequirementListFaults context evidence owned failed) :
        ExpressionFormFaults program (stepSize []) context evidence source environment heap
          (.reference name (.declaration instantiation)) requirements coercions
          (.unsatisfiedRequirement failed) heap
    | group
        {size_fault : Nat}
        {context evidence source environment before after inner requirements
          coercions reason}
        (layout : OrdinaryRequirementLayout requirements coercions [])
        (fault : ExpressionFaults program size_fault context evidence source environment
          before inner reason after) :
        ExpressionFormFaults program (stepSize [size_fault]) context evidence source environment before
          (.group inner) requirements coercions reason after
    | tuple
        {size_fault : Nat}
        {context evidence source environment before after elements requirements
          coercions reason}
        (layout : OrdinaryRequirementLayout requirements coercions [])
        (fault : ExpressionsFault program size_fault context evidence source environment
          before elements reason after) :
        ExpressionFormFaults program (stepSize [size_fault]) context evidence source environment before
          (.tuple elements) requirements coercions reason after
    | unaryOperand
        {size_fault : Nat}
        {context evidence source environment before after operator operand
          requirements coercions owned reason}
        (layout : OrdinaryRequirementLayout requirements coercions owned)
        (fault : ExpressionFaults program size_fault context evidence source environment
          before operand reason after) :
        ExpressionFormFaults program (stepSize [size_fault]) context evidence source environment before
          (.unary operator operand) requirements coercions reason after
    | unaryApply
        {size_operand_evaluates size_fault : Nat}
        {context evidence source environment before middle after operator operand
          requirements coercions owned input reason}
        (layout : OrdinaryRequirementLayout requirements coercions owned)
        (operand_evaluates : ExpressionEvaluates program size_operand_evaluates context evidence source
          environment before operand input middle)
        (fault : UnaryOperationFaults program size_fault context evidence middle operator
          owned input reason after) :
        ExpressionFormFaults program (stepSize [size_operand_evaluates, size_fault]) context evidence source environment before
          (.unary operator operand) requirements coercions reason after
    | binaryLeft
        {size_fault : Nat}
        {context evidence source environment before after left operator right
          requirements coercions owned reason}
        (layout : OrdinaryRequirementLayout requirements coercions owned)
        (fault : ExpressionFaults program size_fault context evidence source environment
          before left reason after) :
        ExpressionFormFaults program (stepSize [size_fault]) context evidence source environment before
          (.binary left operator right) requirements coercions reason after
    | binaryLeftOperand
        {size_left_evaluates : Nat}
        {context evidence source environment before after left operator right
          requirements coercions owned leftValue}
        (layout : OrdinaryRequirementLayout requirements coercions owned)
        (left_evaluates : ExpressionEvaluates program size_left_evaluates context evidence source
          environment before left leftValue after)
        (invalid : BinaryLeftOperandInvalid operator leftValue) :
        ExpressionFormFaults program (stepSize [size_left_evaluates]) context evidence source environment before
          (.binary left operator right) requirements coercions
          (.invalidBinaryOperands operator) after
    | binaryRight
        {size_left_evaluates size_fault : Nat}
        {context evidence source environment before leftHeap after left operator
          right requirements coercions owned leftValue reason}
        (layout : OrdinaryRequirementLayout requirements coercions owned)
        (left_evaluates : ExpressionEvaluates program size_left_evaluates context evidence source
          environment before left leftValue leftHeap)
        (evaluate_right : EvaluatesRightOperand operator leftValue)
        (fault : ExpressionFaults program size_fault context evidence source environment
          leftHeap right reason after) :
        ExpressionFormFaults program (stepSize [size_left_evaluates, size_fault]) context evidence source environment before
          (.binary left operator right) requirements coercions reason after
    | binaryApply
        {size_left_evaluates size_right_evaluates size_fault : Nat}
        {context evidence source environment before leftHeap rightHeap after left
          operator right requirements coercions owned leftValue rightValue reason}
        (layout : OrdinaryRequirementLayout requirements coercions owned)
        (left_evaluates : ExpressionEvaluates program size_left_evaluates context evidence source
          environment before left leftValue leftHeap)
        (evaluate_right : EvaluatesRightOperand operator leftValue)
        (right_evaluates : ExpressionEvaluates program size_right_evaluates context evidence source
          environment leftHeap right rightValue rightHeap)
        (fault : BinaryOperationFaults program size_fault context evidence rightHeap operator
          owned leftValue rightValue reason after) :
        ExpressionFormFaults program (stepSize [size_left_evaluates, size_right_evaluates, size_fault]) context evidence source environment before
          (.binary left operator right) requirements coercions reason after
    | conditionalCondition
        {size_fault : Nat}
        {context evidence source environment before after condition thenBranch
          elseBranch requirements coercions reason}
        (layout : OrdinaryRequirementLayout requirements coercions [])
        (fault : ExpressionFaults program size_fault context evidence source environment
          before condition reason after) :
        ExpressionFormFaults program (stepSize [size_fault]) context evidence source environment before
          (.conditional condition thenBranch elseBranch) requirements coercions
          reason after
    | conditionalType
        {size_condition_evaluates : Nat}
        {context evidence source environment before after condition thenBranch
          elseBranch requirements coercions value actual}
        (layout : OrdinaryRequirementLayout requirements coercions [])
        (condition_evaluates : ExpressionEvaluates program size_condition_evaluates context evidence source
          environment before condition value after)
        (not_boolean : ¬ BooleanValue value)
        (actual_type : ValueRuntimeType value actual) :
        ExpressionFormFaults program (stepSize [size_condition_evaluates]) context evidence source environment before
          (.conditional condition thenBranch elseBranch) requirements coercions
          (.typeMismatch .bool actual) after
    | conditionalTrueBranch
        {size_condition_evaluates size_fault : Nat}
        {context evidence source environment before middle after condition
          thenBranch elseBranch requirements coercions reason}
        (layout : OrdinaryRequirementLayout requirements coercions [])
        (condition_evaluates : ExpressionEvaluates program size_condition_evaluates context evidence source
          environment before condition (.bool true) middle)
        (fault : ExpressionFaults program size_fault context evidence source environment
          middle thenBranch reason after) :
        ExpressionFormFaults program (stepSize [size_condition_evaluates, size_fault]) context evidence source environment before
          (.conditional condition thenBranch elseBranch) requirements coercions
          reason after
    | conditionalFalseBranch
        {size_condition_evaluates size_fault : Nat}
        {context evidence source environment before middle after condition
          thenBranch elseBranch requirements coercions reason}
        (layout : OrdinaryRequirementLayout requirements coercions [])
        (condition_evaluates : ExpressionEvaluates program size_condition_evaluates context evidence source
          environment before condition (.bool false) middle)
        (fault : ExpressionFaults program size_fault context evidence source environment
          middle elseBranch reason after) :
        ExpressionFormFaults program (stepSize [size_condition_evaluates, size_fault]) context evidence source environment before
          (.conditional condition thenBranch elseBranch) requirements coercions
          reason after
    | directCalleeMissing
        {context evidence source environment heap callee arguments instantiation
          requirements coercions}
        (absent : ExpressionMissing source callee) :
        ExpressionFormFaults program (stepSize []) context evidence source environment heap
          (.call callee arguments (.declaration instantiation)) requirements
          coercions (.missingExpression callee) heap
    | directArguments
        {size_fault : Nat}
        {context evidence source environment before after callee arguments
          instantiation requirements coercions calleeNode name reason}
        (callee_contains : ContainsExpression source callee calleeNode)
        (callee_form : calleeNode.form =
          .reference name (.declaration instantiation))
        (fault : ExpressionsFault program size_fault context evidence source environment
          before arguments reason after) :
        ExpressionFormFaults program (stepSize [size_fault]) context evidence source environment before
          (.call callee arguments (.declaration instantiation)) requirements
          coercions reason after
    | directRequirements
        {size_arguments_evaluate : Nat}
        {context evidence source environment before after callee arguments
          instantiation requirements coercions argumentValues failed}
        (arguments_evaluate : ExpressionsEvaluate program size_arguments_evaluate context evidence source
          environment before arguments argumentValues after)
        (fault : RequirementsFault context evidence requirements
          instantiation.predicates failed) :
        ExpressionFormFaults program (stepSize [size_arguments_evaluate]) context evidence source environment before
          (.call callee arguments (.declaration instantiation)) requirements
          coercions (.unsatisfiedRequirement failed) after
    | directApply
        {size_arguments_evaluate size_fault : Nat}
        {context evidence source environment before argumentsHeap after callee
          arguments instantiation requirements coercions argumentValues
          calleeEvidence reason}
        (arguments_evaluate : ExpressionsEvaluate program size_arguments_evaluate context evidence source
          environment before arguments argumentValues argumentsHeap)
        (call_evidence : DirectCallProducesEvidence context evidence requirements
          coercions instantiation.predicates calleeEvidence)
        (fault : CallableFaults program size_fault context evidence calleeEvidence
          argumentsHeap (.global ⟨instantiation, calleeEvidence⟩) argumentValues
          reason after) :
        ExpressionFormFaults program (stepSize [size_arguments_evaluate, size_fault]) context evidence source environment before
          (.call callee arguments (.declaration instantiation)) requirements
          coercions reason after
    | builtinArguments
        {size_fault : Nat}
        {context evidence source environment before after callee
          arguments function requirements coercions reason}
        (layout : OrdinaryRequirementLayout requirements coercions [])
        (fault : ExpressionsFault program size_fault context evidence source environment
          before arguments reason after) :
        ExpressionFormFaults program (stepSize [size_fault]) context evidence source environment before
          (.call callee arguments (.builtinFunction function)) requirements
          coercions reason after
    | builtinApply
        {size_arguments_evaluate size_fault : Nat}
        {context evidence source environment before argumentsHeap after
          callee arguments function requirements coercions argumentValues reason}
        (layout : OrdinaryRequirementLayout requirements coercions [])
        (arguments_evaluate : ExpressionsEvaluate program size_arguments_evaluate context evidence source
          environment before arguments argumentValues argumentsHeap)
        (fault : CallableFaults program size_fault context evidence [] argumentsHeap
          (.builtin ⟨function⟩) argumentValues reason after) :
        ExpressionFormFaults program (stepSize [size_arguments_evaluate, size_fault]) context evidence source environment before
          (.call callee arguments (.builtinFunction function)) requirements
          coercions reason after
    | indirectCallee
        {size_fault : Nat}
        {context evidence source environment before after callee arguments metadata
          requirements coercions reason}
        (fault : ExpressionFaults program size_fault context evidence source environment
          before callee reason after) :
        ExpressionFormFaults program (stepSize [size_fault]) context evidence source environment before
          (.call callee arguments (.indirect metadata)) requirements coercions
          reason after
    | indirectNotCallable
        {size_callee_evaluates : Nat}
        {context evidence source environment before after callee arguments metadata
          requirements coercions callable}
        (callee_evaluates : ExpressionEvaluates program size_callee_evaluates context evidence source
          environment before callee callable after)
        (not_callable : ¬ CallableValue callable) :
        ExpressionFormFaults program (stepSize [size_callee_evaluates]) context evidence source environment before
          (.call callee arguments (.indirect metadata)) requirements coercions
          .notCallable after
    | indirectArguments
        {size_callee_evaluates size_fault : Nat}
        {context evidence source environment before calleeHeap after callee arguments
          metadata requirements coercions callable reason}
        (callee_evaluates : ExpressionEvaluates program size_callee_evaluates context evidence source
          environment before callee callable calleeHeap)
        (callable_shape : CallableValue callable)
        (fault : ExpressionsFault program size_fault context evidence source environment
          calleeHeap arguments reason after) :
        ExpressionFormFaults program (stepSize [size_callee_evaluates, size_fault]) context evidence source environment before
          (.call callee arguments (.indirect metadata)) requirements coercions
          reason after
    | indirectSourceArity
        {size_callee_evaluates size_arguments_evaluate : Nat}
        {context evidence source environment before calleeHeap argumentsHeap callee
          arguments metadata requirements coercions callable argumentValues}
        (callee_evaluates : ExpressionEvaluates program size_callee_evaluates context evidence source
          environment before callee callable calleeHeap)
        (arguments_evaluate : ExpressionsEvaluate program size_arguments_evaluate context evidence source
          environment calleeHeap arguments argumentValues argumentsHeap)
        (mismatch : metadata.argumentCount ≠ arguments.length) :
        ExpressionFormFaults program (stepSize [size_callee_evaluates, size_arguments_evaluate]) context evidence source environment before
          (.call callee arguments (.indirect metadata)) requirements coercions
          (.argumentArityMismatch metadata.argumentCount arguments.length)
          argumentsHeap
    | indirectArgumentCoercion
        {size_callee_evaluates size_arguments_evaluate size_fault : Nat}
        {context evidence source environment before calleeHeap argumentHeap after
          callee arguments metadata requirements coercions callable argumentValues
          packed reason}
        (callee_evaluates : ExpressionEvaluates program size_callee_evaluates context evidence source
          environment before callee callable calleeHeap)
        (arguments_evaluate : ExpressionsEvaluate program size_arguments_evaluate context evidence source
          environment calleeHeap arguments argumentValues argumentHeap)
        (source_arity : arguments.length = metadata.argumentCount)
        (pack : ValuesPack argumentValues packed)
        (fault : CoercionPathFaults program size_fault context evidence argumentHeap
          metadata.argumentCoercions packed reason after) :
        ExpressionFormFaults program (stepSize [size_callee_evaluates, size_arguments_evaluate, size_fault]) context evidence source environment before
          (.call callee arguments (.indirect metadata)) requirements coercions
          reason after
    | indirectApply
        {size_callee_evaluates size_arguments_evaluate size_argument_coercions size_fault : Nat}
        {context evidence source environment before calleeHeap argumentHeap
          coercedHeap after callee arguments metadata requirements coercions
          callable argumentValues packed coerced appliedArguments reason
          invocationEvidence}
        (callee_evaluates : ExpressionEvaluates program size_callee_evaluates context evidence source
          environment before callee callable calleeHeap)
        (arguments_evaluate : ExpressionsEvaluate program size_arguments_evaluate context evidence source
          environment calleeHeap arguments argumentValues argumentHeap)
        (pack_before : ValuesPack argumentValues packed)
        (argument_coercions : CoercionPathExecutes program size_argument_coercions context evidence
          argumentHeap metadata.argumentCoercions packed coerced coercedHeap)
        (pack_after : ValuesPack appliedArguments coerced)
        (source_arity : arguments.length = metadata.argumentCount)
        (applied_arity : appliedArguments.length = metadata.argumentCount)
        (fault : CallableFaults program size_fault context evidence invocationEvidence
          coercedHeap callable appliedArguments reason after) :
        ExpressionFormFaults program (stepSize [size_callee_evaluates, size_arguments_evaluate, size_argument_coercions, size_fault]) context evidence source environment before
          (.call callee arguments (.indirect metadata)) requirements coercions
          reason after
    | constructorArgument
        {size_fault : Nat}
        {context evidence source environment before after instantiation arguments
          requirements coercions reason}
        (layout : OrdinaryRequirementLayout requirements coercions [])
        (fault : ExpressionsFault program size_fault context evidence source environment
          before arguments reason after) :
        ExpressionFormFaults program (stepSize [size_fault]) context evidence source environment before
          (.constructor instantiation arguments) requirements coercions reason after
    | constructorMetadata
        {context evidence source environment heap instantiation arguments
          requirements coercions reason}
        (layout : OrdinaryRequirementLayout requirements coercions [])
        (fault : ConstructorMetadataFaults context instantiation reason) :
        ExpressionFormFaults program (stepSize []) context evidence source environment heap
          (.constructor instantiation arguments) requirements coercions
          reason heap
    | memberBase
        {size_fault : Nat}
        {context evidence source environment before after base name index
          requirements coercions reason}
        (layout : OrdinaryRequirementLayout requirements coercions [])
        (fault : ExpressionFaults program size_fault context evidence source environment
          before base reason after) :
        ExpressionFormFaults program (stepSize [size_fault]) context evidence source environment before
          (.member base name index) requirements coercions reason after
    | memberShape
        {size_base_evaluates : Nat}
        {context evidence source environment before after base name index
          requirements coercions value}
        (layout : OrdinaryRequirementLayout requirements coercions [])
        (base_evaluates : ExpressionEvaluates program size_base_evaluates context evidence source
          environment before base value after)
        (not_constructed : ¬ ConstructedValue value) :
        ExpressionFormFaults program (stepSize [size_base_evaluates]) context evidence source environment before
          (.member base name index) requirements coercions .invalidProjection after
    | memberIndex
        {size_base_evaluates : Nat}
        {context evidence source environment before after base name index
          requirements coercions instantiation arguments}
        (layout : OrdinaryRequirementLayout requirements coercions [])
        (base_evaluates : ExpressionEvaluates program size_base_evaluates context evidence source
          environment before base (.constructed instantiation arguments) after)
        (missing : ValueIndexMissing arguments index) :
        ExpressionFormFaults program (stepSize [size_base_evaluates]) context evidence source environment before
          (.member base name index) requirements coercions .invalidProjection after
    | indexBase
        {size_fault : Nat}
        {context evidence source environment before after base index requirements
          coercions reason}
        (layout : OrdinaryRequirementLayout requirements coercions [])
        (fault : ExpressionFaults program size_fault context evidence source environment
          before base reason after) :
        ExpressionFormFaults program (stepSize [size_fault]) context evidence source environment before
          (.index base index) requirements coercions reason after
    | indexKey
        {size_base_evaluates size_fault : Nat}
        {context evidence source environment before middle after base index
          requirements coercions baseValue reason}
        (layout : OrdinaryRequirementLayout requirements coercions [])
        (base_evaluates : ExpressionEvaluates program size_base_evaluates context evidence source
          environment before base baseValue middle)
        (fault : ExpressionFaults program size_fault context evidence source environment
          middle index reason after) :
        ExpressionFormFaults program (stepSize [size_base_evaluates, size_fault]) context evidence source environment before
          (.index base index) requirements coercions reason after
    | indexShape
        {size_base_evaluates size_index_evaluates : Nat}
        {context evidence source environment before middle after base index
          requirements coercions baseValue key}
        (layout : OrdinaryRequirementLayout requirements coercions [])
        (base_evaluates : ExpressionEvaluates program size_base_evaluates context evidence source
          environment before base baseValue middle)
        (index_evaluates : ExpressionEvaluates program size_index_evaluates context evidence source
          environment middle index key after)
        (not_mapping : ¬ MappingValue baseValue) :
        ExpressionFormFaults program (stepSize [size_base_evaluates, size_index_evaluates]) context evidence source environment before
          (.index base index) requirements coercions .invalidProjection after
    | indexKeyType
        {size_base_evaluates size_index_evaluates : Nat}
        {context evidence source environment before middle after base index
          requirements coercions keyType valueType entries key actual}
        (layout : OrdinaryRequirementLayout requirements coercions [])
        (base_evaluates : ExpressionEvaluates program size_base_evaluates context evidence source
          environment before base (.mapping keyType valueType entries) middle)
        (index_evaluates : ExpressionEvaluates program size_index_evaluates context evidence source
          environment middle index key after)
        (actual_type : ValueRuntimeType key actual)
        (mismatch : runtimeType actual ≠ runtimeType keyType) :
        ExpressionFormFaults program (stepSize [size_base_evaluates, size_index_evaluates]) context evidence source environment before
          (.index base index) requirements coercions
          (.typeMismatch keyType (runtimeType actual)) after
    | indexDefaultUnavailable
        {size_base_evaluates size_index_evaluates : Nat}
        {context evidence source environment before middle after base index
          requirements coercions keyType valueType entries key}
        (layout : OrdinaryRequirementLayout requirements coercions [])
        (base_evaluates : ExpressionEvaluates program size_base_evaluates context evidence source
          environment before base (.mapping keyType valueType entries) middle)
        (index_evaluates : ExpressionEvaluates program size_index_evaluates context evidence source
          environment middle index key after)
        (key_type : ValueRuntimeTypeMatches key keyType)
        (absent : MappingAbsent key entries)
        (not_defaultable : ¬ Defaultable valueType) :
        ExpressionFormFaults program (stepSize [size_base_evaluates, size_index_evaluates]) context evidence source environment before
          (.index base index) requirements coercions
          (.missingMappingDefault valueType) after

  inductive ExpressionsFault (program : Program) : Nat →
      Context → EvidenceEnvironment → TypedSource → Dynamic.Environment →
        Heap → List ExpressionId → SemanticFault → Heap → Prop where
    | head
        {size_fault : Nat}
        {context evidence source environment before after expression expressions
          reason}
        (fault : ExpressionFaults program size_fault context evidence source environment
          before expression reason after) :
        ExpressionsFault program (stepSize [size_fault]) context evidence source environment before
          (expression :: expressions) reason after
    | tail
        {size_head size_fault : Nat}
        {context evidence source environment before middle after expression
          expressions value reason}
        (head : ExpressionEvaluates program size_head context evidence source environment
          before expression value middle)
        (fault : ExpressionsFault program size_fault context evidence source environment
          middle expressions reason after) :
        ExpressionsFault program (stepSize [size_head, size_fault]) context evidence source environment before
          (expression :: expressions) reason after

  inductive UnaryOperationFaults (program : Program) : Nat →
      Context → EvidenceEnvironment → Heap → Syntax.UnaryOp →
        List RequirementId → Value → SemanticFault → Heap → Prop where
    | primitive
        {context evidence heap operator input}
        (invalid : UnaryPrimitiveOperandInvalid operator input) :
        UnaryOperationFaults program (stepSize []) context evidence heap operator [] input
          (.invalidUnaryOperand operator) heap
    | requirement
        {context evidence heap operator requirements input failed}
        (fault : RequirementListFaults context evidence requirements failed) :
        UnaryOperationFaults program (stepSize []) context evidence heap operator requirements
          input (.unsatisfiedRequirement failed) heap
    | method
        {size_fault : Nat}
        {context evidence before after operator requirements input traitName
          methodName bodyInstance calleeEvidence reason}
        (dispatch : UnaryTraitDispatch operator traitName methodName)
        (selected : OperatorMethodSelected program context evidence traitName
          methodName requirements bodyInstance calleeEvidence)
        (fault : BodyFaults program size_fault bodyInstance calleeEvidence before [input]
          reason after) :
        UnaryOperationFaults program (stepSize [size_fault]) context evidence before operator requirements
          input reason after

  inductive BinaryOperationFaults (program : Program) : Nat →
      Context → EvidenceEnvironment → Heap → Syntax.BinaryOp →
        List RequirementId → Value → Value → SemanticFault → Heap → Prop where
    | primitive
        {context evidence heap operator left right}
        (invalid : BinaryPrimitiveOperandsInvalid operator left right) :
        BinaryOperationFaults program (stepSize []) context evidence heap operator [] left right
          (.invalidBinaryOperands operator) heap
    | requirement
        {context evidence heap operator requirements left right failed}
        (fault : RequirementListFaults context evidence requirements failed) :
        BinaryOperationFaults program (stepSize []) context evidence heap operator requirements
          left right (.unsatisfiedRequirement failed) heap
    | method
        {size_fault : Nat}
        {context evidence before after operator requirements left right traitName
          methodName bodyInstance calleeEvidence reason}
        (dispatch : BinaryTraitDispatch operator traitName methodName)
        (selected : OperatorMethodSelected program context evidence traitName
          methodName requirements bodyInstance calleeEvidence)
        (fault : BodyFaults program size_fault bodyInstance calleeEvidence before [left, right]
          reason after) :
        BinaryOperationFaults program (stepSize [size_fault]) context evidence before operator requirements
          left right reason after

  inductive CoercionStepFaults (program : Program) : Nat →
      Context → EvidenceEnvironment → Heap → CoercionStep → Value →
        SemanticFault → Heap → Prop where
    | requirement
        {context evidence heap step input failed}
        (fault : RequirementListFaults context evidence step.requirements failed) :
        CoercionStepFaults program (stepSize []) context evidence heap step input
          (.unsatisfiedRequirement failed) heap
    | primitiveInput
        {context evidence heap step input actual}
        (no_source_method : ∀ bodyInstance calleeEvidence,
          ¬ OperatorMethodSelected program context evidence "Coerce" "coerce"
            step.requirements bodyInstance calleeEvidence)
        (invalid : PrimitiveCoercionInputInvalid step input)
        (actual_type : ValueRuntimeType input actual) :
        CoercionStepFaults program (stepSize []) context evidence heap step input
          (.typeMismatch step.source actual) heap
    | method
        {size_fault : Nat}
        {context evidence before after step input bodyInstance calleeEvidence reason}
        (selected : OperatorMethodSelected program context evidence "Coerce"
          "coerce" step.requirements bodyInstance calleeEvidence)
        (fault : BodyFaults program size_fault bodyInstance calleeEvidence before [input]
          reason after) :
        CoercionStepFaults program (stepSize [size_fault]) context evidence before step input reason after

  inductive CoercionPathFaults (program : Program) : Nat →
      Context → EvidenceEnvironment → Heap → List CoercionStep → Value →
        SemanticFault → Heap → Prop where
    | head
        {size_fault : Nat}
        {context evidence before after step steps input reason}
        (fault : CoercionStepFaults program size_fault context evidence before step input
          reason after) :
        CoercionPathFaults program (stepSize [size_fault]) context evidence before (step :: steps) input
          reason after
    | tail
        {size_head size_fault : Nat}
        {context evidence before middle after step steps input converted reason}
        (head : CoercionStepExecutes program size_head context evidence before step input
          converted middle)
        (fault : CoercionPathFaults program size_fault context evidence middle steps converted
          reason after) :
        CoercionPathFaults program (stepSize [size_head, size_fault]) context evidence before (step :: steps) input
          reason after

  inductive CallableFaults (program : Program) : Nat →
      Context → EvidenceEnvironment → EvidenceEnvironment → Heap →
        Value → List Value → SemanticFault → Heap → Prop where
    | notCallable
        {context callerEvidence invocationEvidence heap callable arguments}
        (invalid : ¬ CallableValue callable) :
        CallableFaults program (stepSize []) context callerEvidence invocationEvidence heap
          callable arguments .notCallable heap
    | builtinArity
        {context callerEvidence invocationEvidence heap function arguments}
        (mismatch : function.id.parameterTypes.length ≠ arguments.length) :
        CallableFaults program (stepSize []) context callerEvidence invocationEvidence heap
          (.builtin function) arguments
          (.argumentArityMismatch function.id.parameterTypes.length
            arguments.length) heap
    | builtinArgumentType
        {context callerEvidence invocationEvidence heap function arguments
          expected actual}
        (arity : function.id.parameterTypes.length = arguments.length)
        (mismatch : ValuesFirstTypeMismatch arguments function.id.parameterTypes
          expected actual) :
        CallableFaults program (stepSize []) context callerEvidence invocationEvidence heap
          (.builtin function) arguments (.typeMismatch expected actual) heap
    | globalSignatureMissing
        {context callerEvidence invocationEvidence heap function arguments}
        (missing : FunctionSignatureMissing program
          function.instantiation.declaration) :
        CallableFaults program (stepSize []) context callerEvidence invocationEvidence heap
          (.global function) arguments
          (.missingDeclaration function.instantiation.declaration) heap
    | globalBodyMissing
        {context callerEvidence invocationEvidence heap function arguments}
        (missing : FunctionBodyMissing program function.instantiation.declaration) :
        CallableFaults program (stepSize []) context callerEvidence invocationEvidence heap
          (.global function) arguments
          (.missingDeclaration function.instantiation.declaration) heap
    | globalArity
        {context callerEvidence invocationEvidence heap function arguments
          bodyInstance}
        (instantiates : FunctionInstantiates program function.instantiation
          bodyInstance)
        (mismatch : bodyInstance.source.inputs.length ≠ arguments.length) :
        CallableFaults program (stepSize []) context callerEvidence invocationEvidence heap
          (.global function) arguments
          (.argumentArityMismatch bodyInstance.source.inputs.length
            arguments.length) heap
    | globalBody
        {size_fault : Nat}
        {context callerEvidence invocationEvidence before after function arguments
          bodyInstance reason}
        (instantiates : FunctionInstantiates program function.instantiation
          bodyInstance)
        (invocation_eq : invocationEvidence = function.evidence)
        (fault : BodyFaults program size_fault bodyInstance invocationEvidence before arguments
          reason after) :
        CallableFaults program (stepSize [size_fault]) context callerEvidence invocationEvidence before
          (.global function) arguments reason after
    | closureArity
        {context callerEvidence invocationEvidence heap function arguments}
        (mismatch : function.parameters.length ≠ arguments.length) :
        CallableFaults program (stepSize []) context callerEvidence invocationEvidence heap
          (.closure function) arguments
          (.argumentArityMismatch function.parameters.length arguments.length) heap
    | closureBody
        {size_fault : Nat}
        {context callerEvidence invocationEvidence before bound after function
          arguments environment parameterTypes callContext finalContext reason}
        (invocation_eq : invocationEvidence = function.evidence)
        (frame : ClosureFrame program function)
        (parameters_extend : MonoBindersExtend function.source.owner
          function.context function.parameters parameterTypes callContext)
        (allocate : BindersAllocate function.captured before function.parameters
          arguments environment bound)
        (fault : FunctionStatementsFault program size_fault callContext function.evidence
          function.source environment bound function.body finalContext reason after) :
        CallableFaults program (stepSize [size_fault]) context callerEvidence invocationEvidence before
          (.closure function) arguments reason after
    | closureControlEscape
        {size_execute : Nat}
        {context callerEvidence invocationEvidence before bound after function
          arguments environment parameterTypes callContext finalContext outcome}
        (invocation_eq : invocationEvidence = function.evidence)
        (frame : ClosureFrame program function)
        (parameters_extend : MonoBindersExtend function.source.owner
          function.context function.parameters parameterTypes callContext)
        (allocate : BindersAllocate function.captured before function.parameters
          arguments environment bound)
        (execute : FunctionStatementsExecute program size_execute callContext function.evidence
          function.source environment bound function.body finalContext outcome after)
        (escaped : (∃ escapedEnvironment, outcome = .breaking escapedEnvironment) ∨
          (∃ escapedEnvironment, outcome = .continuing escapedEnvironment)) :
        CallableFaults program (stepSize [size_execute]) context callerEvidence invocationEvidence before
          (.closure function) arguments .controlEscapedFunction after

  inductive BodyFaults (program : Program) : Nat →
      BodyInstance → EvidenceEnvironment → Heap → List Value →
        SemanticFault → Heap → Prop where
    | arity
        {bodyInstance evidence heap arguments}
        (mismatch : bodyInstance.source.inputs.length ≠ arguments.length) :
        BodyFaults program (stepSize []) bodyInstance evidence heap arguments
          (.argumentArityMismatch bodyInstance.source.inputs.length
            arguments.length) heap
    | statements
        {size_fault : Nat}
        {bodyInstance evidence before bound after arguments environment roots
          inputTypes lexicalContext finalContext reason}
        (roots_eq : StatementRoots bodyInstance.source.roots roots)
        (inputs_extend : MonoBindersExtend bodyInstance.source.owner
          bodyInstance.context bodyInstance.source.inputs inputTypes lexicalContext)
        (allocate : BindersAllocate [] before bodyInstance.source.inputs arguments
          environment bound)
        (fault : FunctionStatementsFault program size_fault lexicalContext evidence
          bodyInstance.source environment bound roots finalContext reason after) :
        BodyFaults program (stepSize [size_fault]) bodyInstance evidence before arguments reason after
    | controlEscape
        {size_execute : Nat}
        {bodyInstance evidence before bound after arguments environment roots outcome
          inputTypes lexicalContext finalContext}
        (roots_eq : StatementRoots bodyInstance.source.roots roots)
        (inputs_extend : MonoBindersExtend bodyInstance.source.owner
          bodyInstance.context bodyInstance.source.inputs inputTypes lexicalContext)
        (allocate : BindersAllocate [] before bodyInstance.source.inputs arguments
          environment bound)
        (execute : FunctionStatementsExecute program size_execute lexicalContext evidence
          bodyInstance.source environment bound roots finalContext outcome after)
        (escaped : (∃ escapedEnvironment, outcome = .breaking escapedEnvironment) ∨
          (∃ escapedEnvironment, outcome = .continuing escapedEnvironment)) :
        BodyFaults program (stepSize [size_execute]) bodyInstance evidence before arguments
          .controlEscapedFunction after

  inductive StatementFaults (program : Program) : Nat →
      Context → EvidenceEnvironment → TypedSource → Dynamic.Environment →
        Heap → StatementId → SemanticFault → Heap → Prop where
    | missing
        {context evidence source environment heap id}
        (absent : StatementMissing source id) :
        StatementFaults program (stepSize []) context evidence source environment heap id
          (.missingStatement id) heap
    | polymorphicLet
        {context evidence source environment heap id node binder initializer}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .letDecl binder initializer)
        (polymorphic : binder.scheme.quantified ≠ [])
        (unsupported : GeneralizedInitializerUnsupported source binder
          initializer) :
        StatementFaults program (stepSize []) context evidence source environment heap id
          (.unsupportedPolymorphicBinder binder.id) heap
    | letInitializer
        {size_fault : Nat}
        {context evidence source environment before after id node binder initializer
          reason}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .letDecl binder (some initializer))
        (monomorphic : binder.scheme.quantified = [])
        (fault : ExpressionFaults program size_fault context evidence source environment
          before initializer reason after) :
        StatementFaults program (stepSize [size_fault]) context evidence source environment before id
          reason after
    | returnValue
        {size_fault : Nat}
        {context evidence source environment before after id node expression reason}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .returnStmt (some expression))
        (fault : ExpressionFaults program size_fault context evidence source environment
          before expression reason after) :
        StatementFaults program (stepSize [size_fault]) context evidence source environment before id
          reason after
    | expression
        {size_fault : Nat}
        {context evidence source environment before after id node expression
          semicolon reason}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .expression expression semicolon)
        (fault : ExpressionFaults program size_fault context evidence source environment
          before expression reason after) :
        StatementFaults program (stepSize [size_fault]) context evidence source environment before id
          reason after
    | assignValue
        {size_fault : Nat}
        {context evidence source environment before after id node assignment
          operator rhs reason}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .assignValue assignment operator rhs)
        (fault : SourcePlaceAssignmentFaults program size_fault context evidence source
          environment before assignment.target operator rhs reason after) :
        StatementFaults program (stepSize [size_fault]) context evidence source environment before id
          reason after
    | assignBitNot
        {size_fault : Nat}
        {context evidence source environment before after id node assignment reason}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .assignBitNot assignment)
        (fault : SourcePlaceBitNotFaults program size_fault context evidence source environment
          before assignment.target reason after) :
        StatementFaults program (stepSize [size_fault]) context evidence source environment before id
          reason after
    | ifCondition
        {size_fault : Nat}
        {context evidence source environment before after id node condition thenBody
          elseBody reason}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .ifThen condition thenBody elseBody)
        (fault : ExpressionFaults program size_fault context evidence source environment
          before condition reason after) :
        StatementFaults program (stepSize [size_fault]) context evidence source environment before id
          reason after
    | ifConditionType
        {size_evaluate : Nat}
        {context evidence source environment before after id node condition thenBody
          elseBody value actual}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .ifThen condition thenBody elseBody)
        (evaluate : ExpressionEvaluates program size_evaluate context evidence source environment
          before condition value after)
        (not_boolean : ¬ BooleanValue value)
        (actual_type : ValueRuntimeType value actual) :
        StatementFaults program (stepSize [size_evaluate]) context evidence source environment before id
          (.typeMismatch .bool actual) after
    | ifTrueBody
        {size_evaluate size_fault : Nat}
        {context evidence source environment before middle after id node condition
          thenBody elseBody finalContext reason}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .ifThen condition thenBody elseBody)
        (evaluate : ExpressionEvaluates program size_evaluate context evidence source environment
          before condition (.bool true) middle)
        (fault : StatementsFault program size_fault context evidence source environment middle
          thenBody finalContext reason after) :
        StatementFaults program (stepSize [size_evaluate, size_fault]) context evidence source environment before id
          reason after
    | ifFalseBody
        {size_evaluate size_fault : Nat}
        {context evidence source environment before middle after id node condition
          thenBody body finalContext reason}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .ifThen condition thenBody (some body))
        (evaluate : ExpressionEvaluates program size_evaluate context evidence source environment
          before condition (.bool false) middle)
        (fault : StatementsFault program size_fault context evidence source environment middle
          body finalContext reason after) :
        StatementFaults program (stepSize [size_evaluate, size_fault]) context evidence source environment before id
          reason after
    | block
        {size_fault : Nat}
        {context evidence source environment before after id node body finalContext
          reason}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .block body)
        (fault : StatementsFault program size_fault context evidence source environment before
          body finalContext reason after) :
        StatementFaults program (stepSize [size_fault]) context evidence source environment before id
          reason after
    | matchScrutinee
        {size_fault : Nat}
        {context evidence source environment before after id node resolution reason}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .matchWith resolution)
        (fault : ExpressionFaults program size_fault context evidence source environment
          before resolution.scrutinee reason after) :
        StatementFaults program (stepSize [size_fault]) context evidence source environment before id
          reason after
    | matchPattern
        {size_scrutinee_evaluates : Nat}
        {context evidence source environment before scrutineeHeap hiddenHeap id node
          resolution scrutinee scrutineeNode location}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .matchWith resolution)
        (scrutinee_contains : ContainsExpression source resolution.scrutinee
          scrutineeNode)
        (scrutinee_evaluates : ExpressionEvaluates program size_scrutinee_evaluates context evidence source
          environment before resolution.scrutinee scrutinee scrutineeHeap)
        (allocate_hidden : Heap.Allocates scrutineeHeap scrutineeNode.type
          (some scrutinee) location hiddenHeap)
        (fault : MatchCasesPatternFault context scrutinee resolution.cases) :
        StatementFaults program (stepSize [size_scrutinee_evaluates]) context evidence source environment before id
          .invalidPattern hiddenHeap
    | matchArmBody
        {size_scrutinee_evaluates size_fault : Nat}
        {context evidence source environment before scrutineeHeap hiddenHeap after id
          node resolution scrutinee scrutineeNode location armBody bindings binders
          values armContext armEnvironment bound finalContext reason}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .matchWith resolution)
        (scrutinee_contains : ContainsExpression source resolution.scrutinee
          scrutineeNode)
        (scrutinee_evaluates : ExpressionEvaluates program size_scrutinee_evaluates context evidence source
          environment before resolution.scrutinee scrutinee scrutineeHeap)
        (allocate_hidden : Heap.Allocates scrutineeHeap scrutineeNode.type
          (some scrutinee) location hiddenHeap)
        (select : MatchCasesSelect context scrutinee resolution.cases
          resolution.defaultBody (.arm armBody bindings))
        (binders_eq : binders = bindings.map Prod.fst)
        (values_eq : values = bindings.map Prod.snd)
        (binders_extend : BindersExtend source.owner context binders armContext)
        (allocate_bindings : BindersAllocate environment hiddenHeap binders values
          armEnvironment bound)
        (fault : StatementsFault program size_fault armContext evidence source armEnvironment
          bound armBody finalContext reason after) :
        StatementFaults program (stepSize [size_scrutinee_evaluates, size_fault]) context evidence source environment before id
          reason after
    | matchDefaultBody
        {size_scrutinee_evaluates size_fault : Nat}
        {context evidence source environment before scrutineeHeap hiddenHeap after id
          node resolution scrutinee scrutineeNode location body finalContext reason}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .matchWith resolution)
        (scrutinee_contains : ContainsExpression source resolution.scrutinee
          scrutineeNode)
        (scrutinee_evaluates : ExpressionEvaluates program size_scrutinee_evaluates context evidence source
          environment before resolution.scrutinee scrutinee scrutineeHeap)
        (allocate_hidden : Heap.Allocates scrutineeHeap scrutineeNode.type
          (some scrutinee) location hiddenHeap)
        (select : MatchCasesSelect context scrutinee resolution.cases
          resolution.defaultBody (.default body))
        (fault : StatementsFault program size_fault context evidence source environment
          hiddenHeap body finalContext reason after) :
        StatementFaults program (stepSize [size_scrutinee_evaluates, size_fault]) context evidence source environment before id
          reason after
    | forInitializer
        {size_fault : Nat}
        {context evidence source environment before after id node initializer
          condition post body finalContext reason}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .forLoop initializer condition post body)
        (fault : ForItemsFault program size_fault context evidence source environment before
          initializer finalContext reason after) :
        StatementFaults program (stepSize [size_fault]) context evidence source environment before id
          reason after
    | forIteration
        {size_initializer_executes size_fault : Nat}
        {context evidence source environment before initialized after id node
          initializer condition post body loopContext loopEnvironment reason}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .forLoop initializer condition post body)
        (initializer_executes : ForItemsExecute program size_initializer_executes context evidence source
          environment before initializer loopContext loopEnvironment initialized)
        (fault : ForLoopFaults program size_fault loopContext evidence source loopEnvironment
          initialized condition post body reason after) :
        StatementFaults program (stepSize [size_initializer_executes, size_fault]) context evidence source environment before id
          reason after
    | whileIteration
        {size_fault : Nat}
        {context evidence source environment before after id node condition body
          reason}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .whileLoop condition body)
        (fault : WhileFaults program size_fault context evidence source environment before
          condition body reason after) :
        StatementFaults program (stepSize [size_fault]) context evidence source environment before id
          reason after

  inductive StatementsFault (program : Program) : Nat →
      Context → EvidenceEnvironment → TypedSource → Dynamic.Environment →
        Heap → List StatementId → Context → SemanticFault → Heap → Prop where
    | head
        {size_fault : Nat}
        {context evidence source environment before after statement statements reason}
        (fault : StatementFaults program size_fault context evidence source environment before
          statement reason after) :
        StatementsFault program (stepSize [size_fault]) context evidence source environment before
          (statement :: statements) context reason after
    | tail
        {size_head size_fault : Nat}
        {context middleContext finalContext evidence source environment before
          middle after statement statements nextEnvironment reason}
        (head : StatementExecutes program size_head context evidence source environment before
          statement middleContext (.fallthrough nextEnvironment) middle)
        (fault : StatementsFault program size_fault middleContext evidence source
          nextEnvironment middle statements finalContext reason after) :
        StatementsFault program (stepSize [size_head, size_fault]) context evidence source environment before
          (statement :: statements) finalContext reason after

  inductive FunctionStatementsFault (program : Program) : Nat →
      Context → EvidenceEnvironment → TypedSource → Dynamic.Environment →
        Heap → List StatementId → Context → SemanticFault → Heap → Prop where
    | singleton
        {size_fault : Nat}
        {context evidence source environment before after statement reason}
        (fault : StatementFaults program size_fault context evidence source environment before
          statement reason after) :
        FunctionStatementsFault program (stepSize [size_fault]) context evidence source environment before
          [statement] context reason after
    | tailExpression
        {size_fault : Nat}
        {context evidence source environment before after statement node expression
          reason}
        (contains : ContainsStatement source statement node)
        (form_eq : node.form = .expression expression false)
        (fault : ExpressionFaults program size_fault context evidence source environment
          before expression reason after) :
        FunctionStatementsFault program (stepSize [size_fault]) context evidence source environment before
          [statement] context reason after
    | head
        {size_fault : Nat}
        {context evidence source environment before after statement next rest reason}
        (fault : StatementFaults program size_fault context evidence source environment before
          statement reason after) :
        FunctionStatementsFault program (stepSize [size_fault]) context evidence source environment before
          (statement :: next :: rest) context reason after
    | tail
        {size_head size_fault : Nat}
        {context middleContext finalContext evidence source environment before
          middle after statement next rest nextEnvironment reason}
        (head : StatementExecutes program size_head context evidence source environment before
          statement middleContext (.fallthrough nextEnvironment) middle)
        (fault : FunctionStatementsFault program size_fault middleContext evidence source
          nextEnvironment middle (next :: rest) finalContext reason after) :
        FunctionStatementsFault program (stepSize [size_head, size_fault]) context evidence source environment before
          (statement :: next :: rest) finalContext reason after

  inductive SourcePlaceFaults (program : Program) : Nat →
      Context → EvidenceEnvironment → TypedSource → Dynamic.Environment → Heap →
        PlaceResolution → SemanticFault → Heap → Prop where
    | unbound
        {context evidence source environment heap place}
        (missing : environment.Unbound place.root) :
        SourcePlaceFaults program (stepSize []) context evidence source environment heap place
          (.unboundLocal place.root) heap
    | dangling
        {context evidence source environment heap place location}
        (lookup : Dynamic.Environment.LooksUp environment place.root location)
        (missing : heap.Dangling location) :
        SourcePlaceFaults program (stepSize []) context evidence source environment heap place
          (.danglingLocation location) heap
    | projectionExpression
        {size_fault : Nat}
        {context evidence source environment before after place location cell reason}
        (lookup : Dynamic.Environment.LooksUp environment place.root location)
        (read : Heap.Reads before location cell)
        (fault : SourceProjectionsFault program size_fault context evidence source environment
          before place.projections reason after) :
        SourcePlaceFaults program (stepSize [size_fault]) context evidence source environment before place
          reason after
    | danglingAfterProjections
        {size_evaluate : Nat}
        {context evidence source environment before after place location cell
          evaluated}
        (lookup : Dynamic.Environment.LooksUp environment place.root location)
        (read : Heap.Reads before location cell)
        (evaluate : SourceProjectionsEvaluate program size_evaluate context evidence source
          environment before place.projections evaluated after)
        (missing : after.Dangling location) :
        SourcePlaceFaults program (stepSize [size_evaluate]) context evidence source environment before place
          (.danglingLocation location) after
    | projectionRead
        {size_evaluate : Nat}
        {context evidence source environment before after place location initialCell
          currentCell evaluated initial reason}
        (lookup : Dynamic.Environment.LooksUp environment place.root location)
        (initial_read : Heap.Reads before location initialCell)
        (evaluate : SourceProjectionsEvaluate program size_evaluate context evidence source
          environment before place.projections evaluated after)
        (current_read : Heap.Reads after location currentCell)
        (initial_value : RootInitialValue currentCell initial)
        (fault : ProjectionsFaults initial evaluated reason) :
        SourcePlaceFaults program (stepSize [size_evaluate]) context evidence source environment before place
          reason after
    | uninitialized
        {size_evaluate : Nat}
        {context evidence source environment before after place location initialCell
          currentCell evaluated}
        (lookup : Dynamic.Environment.LooksUp environment place.root location)
        (initial_read : Heap.Reads before location initialCell)
        (evaluate : SourceProjectionsEvaluate program size_evaluate context evidence source
          environment before place.projections evaluated after)
        (current_read : Heap.Reads after location currentCell)
        (empty : currentCell.value = none)
        (not_mapping : ¬ ∃ keyType valueType,
          currentCell.type = .mapping keyType valueType)
        (has_projection : evaluated ≠ []) :
        SourcePlaceFaults program (stepSize [size_evaluate]) context evidence source environment before place
          (.uninitializedLocation location) after

  inductive SourceProjectionsFault (program : Program) : Nat →
      Context → EvidenceEnvironment → TypedSource → Dynamic.Environment → Heap →
        List PlaceProjection → SemanticFault → Heap → Prop where
    | indexHead
        {size_fault : Nat}
        {context evidence source environment before after expression projections
          reason}
        (fault : ExpressionFaults program size_fault context evidence source environment
          before expression reason after) :
        SourceProjectionsFault program (stepSize [size_fault]) context evidence source environment before
          (.index expression :: projections) reason after
    | indexTail
        {size_head size_fault : Nat}
        {context evidence source environment before middle after expression key
          projections reason}
        (head : ExpressionEvaluates program size_head context evidence source environment
          before expression key middle)
        (fault : SourceProjectionsFault program size_fault context evidence source environment
          middle projections reason after) :
        SourceProjectionsFault program (stepSize [size_head, size_fault]) context evidence source environment before
          (.index expression :: projections) reason after
    | memberTail
        {size_fault : Nat}
        {context evidence source environment before after name index projections
          reason}
        (fault : SourceProjectionsFault program size_fault context evidence source environment
          before projections reason after) :
        SourceProjectionsFault program (stepSize [size_fault]) context evidence source environment before
          (.member name index :: projections) reason after

  inductive SourcePlaceAssignmentFaults (program : Program) : Nat →
      Context → EvidenceEnvironment → TypedSource → Dynamic.Environment → Heap →
        PlaceResolution → Syntax.ValueAssignOp → ExpressionId → SemanticFault →
        Heap → Prop where
    | target
        {size_fault : Nat}
        {context evidence source environment before after place operator rhs reason}
        (fault : SourcePlaceFaults program size_fault context evidence source environment
          before place reason after) :
        SourcePlaceAssignmentFaults program (stepSize [size_fault]) context evidence source environment
          before place operator rhs reason after
    | rhs
        {size_resolve size_fault : Nat}
        {context evidence source environment before targetHeap after place operator
          rhs target reason}
        (resolve : SourcePlaceResolves program size_resolve context evidence source environment
          before place target targetHeap)
        (fault : ExpressionFaults program size_fault context evidence source environment
          targetHeap rhs reason after) :
        SourcePlaceAssignmentFaults program (stepSize [size_resolve, size_fault]) context evidence source environment
          before place operator rhs reason after
    | operands
        {size_resolve size_evaluate : Nat}
        {context evidence source environment before targetHeap rhsHeap place operator
          rhs target right currentCell initial currentSelected}
        (resolve : SourcePlaceResolves program size_resolve context evidence source environment
          before place target targetHeap)
        (evaluate : ExpressionEvaluates program size_evaluate context evidence source environment
          targetHeap rhs right rhsHeap)
        (current_read : Heap.Reads rhsHeap target.location currentCell)
        (root_type_eq : currentCell.type = target.rootType)
        (initial_value : RootInitialValue currentCell initial)
        (path_read : ProjectionsRead initial target.projections currentSelected)
        (invalid : AssignmentOperandsInvalid operator target.selected right) :
        SourcePlaceAssignmentFaults program (stepSize [size_resolve, size_evaluate]) context evidence source environment
          before place operator rhs (.invalidAssignmentOperands operator) rhsHeap
    | structuralUpdate
        {size_resolve size_evaluate : Nat}
        {context evidence source environment before targetHeap rhsHeap place operator
          rhs target right currentCell initial reason}
        (resolve : SourcePlaceResolves program size_resolve context evidence source environment
          before place target targetHeap)
        (evaluate : ExpressionEvaluates program size_evaluate context evidence source environment
          targetHeap rhs right rhsHeap)
        (current_read : Heap.Reads rhsHeap target.location currentCell)
        (root_type_eq : currentCell.type = target.rootType)
        (initial_value : RootInitialValue currentCell initial)
        (fault : ProjectionsFaults initial target.projections reason) :
        SourcePlaceAssignmentFaults program (stepSize [size_resolve, size_evaluate]) context evidence source environment
          before place operator rhs reason rhsHeap

  inductive SourcePlaceBitNotFaults (program : Program) : Nat →
      Context → EvidenceEnvironment → TypedSource → Dynamic.Environment → Heap →
        PlaceResolution → SemanticFault → Heap → Prop where
    | target
        {size_fault : Nat}
        {context evidence source environment before after place reason}
        (fault : SourcePlaceFaults program size_fault context evidence source environment
          before place reason after) :
        SourcePlaceBitNotFaults program (stepSize [size_fault]) context evidence source environment before
          place reason after
    | uninitialized
        {size_resolve : Nat}
        {context evidence source environment before after place target}
        (resolve : SourcePlaceResolves program size_resolve context evidence source environment
          before place target after)
        (empty : target.selected = none) :
        SourcePlaceBitNotFaults program (stepSize [size_resolve]) context evidence source environment before
          place (.invalidUnaryOperand .bitNot) after
    | operand
        {size_resolve : Nat}
        {context evidence source environment before after place target value}
        (resolve : SourcePlaceResolves program size_resolve context evidence source environment
          before place target after)
        (selected : target.selected = some value)
        (invalid : UnaryPrimitiveOperandInvalid .bitNot value) :
        SourcePlaceBitNotFaults program (stepSize [size_resolve]) context evidence source environment before
          place (.invalidUnaryOperand .bitNot) after

  inductive ForItemFaults (program : Program) : Nat →
      Context → EvidenceEnvironment → TypedSource → Dynamic.Environment → Heap →
        ForItemForm → SemanticFault → Heap → Prop where
    | polymorphicLet
        {context evidence source environment heap binder initializer}
        (polymorphic : binder.scheme.quantified ≠ [])
        (unsupported : GeneralizedInitializerUnsupported source binder
          initializer) :
        ForItemFaults program (stepSize []) context evidence source environment heap
          (.letDecl binder initializer)
          (.unsupportedPolymorphicBinder binder.id) heap
    | letInitializer
        {size_fault : Nat}
        {context evidence source environment before after binder initializer reason}
        (monomorphic : binder.scheme.quantified = [])
        (fault : ExpressionFaults program size_fault context evidence source environment
          before initializer reason after) :
        ForItemFaults program (stepSize [size_fault]) context evidence source environment before
          (.letDecl binder (some initializer)) reason after
    | expression
        {size_fault : Nat}
        {context evidence source environment before after expression reason}
        (fault : ExpressionFaults program size_fault context evidence source environment
          before expression reason after) :
        ForItemFaults program (stepSize [size_fault]) context evidence source environment before
          (.expression expression) reason after
    | assignValue
        {size_fault : Nat}
        {context evidence source environment before after assignment operator rhs
          reason}
        (fault : SourcePlaceAssignmentFaults program size_fault context evidence source
          environment before assignment.target operator rhs reason after) :
        ForItemFaults program (stepSize [size_fault]) context evidence source environment before
          (.assignValue assignment operator rhs) reason after
    | assignBitNot
        {size_fault : Nat}
        {context evidence source environment before after assignment reason}
        (fault : SourcePlaceBitNotFaults program size_fault context evidence source environment
          before assignment.target reason after) :
        ForItemFaults program (stepSize [size_fault]) context evidence source environment before
          (.assignBitNot assignment) reason after

  inductive ForItemsFault (program : Program) : Nat →
      Context → EvidenceEnvironment → TypedSource → Dynamic.Environment → Heap →
        List ForItemForm → Context → SemanticFault → Heap → Prop where
    | head
        {size_fault : Nat}
        {context evidence source environment before after item items reason}
        (fault : ForItemFaults program size_fault context evidence source environment before
          item reason after) :
        ForItemsFault program (stepSize [size_fault]) context evidence source environment before
          (item :: items) context reason after
    | tail
        {size_head size_fault : Nat}
        {context middleContext finalContext evidence source environment before
          middle after item items nextEnvironment reason}
        (head : ForItemExecutes program size_head context evidence source environment before
          item middleContext nextEnvironment middle)
        (fault : ForItemsFault program size_fault middleContext evidence source nextEnvironment
          middle items finalContext reason after) :
        ForItemsFault program (stepSize [size_head, size_fault]) context evidence source environment before
          (item :: items) finalContext reason after

  inductive WhileFaults (program : Program) : Nat →
      Context → EvidenceEnvironment → TypedSource → Dynamic.Environment → Heap →
        ExpressionId → List StatementId → SemanticFault → Heap → Prop where
    | condition
        {size_fault : Nat}
        {context evidence source environment before after condition body reason}
        (fault : ExpressionFaults program size_fault context evidence source environment
          before condition reason after) :
        WhileFaults program (stepSize [size_fault]) context evidence source environment before condition
          body reason after
    | conditionType
        {size_evaluate : Nat}
        {context evidence source environment before after condition body value actual}
        (evaluate : ExpressionEvaluates program size_evaluate context evidence source environment
          before condition value after)
        (not_boolean : ¬ BooleanValue value)
        (actual_type : ValueRuntimeType value actual) :
        WhileFaults program (stepSize [size_evaluate]) context evidence source environment before condition
          body (.typeMismatch .bool actual) after
    | body
        {size_condition_evaluates size_fault : Nat}
        {context evidence source environment before conditionHeap after condition
          body finalContext reason}
        (condition_evaluates : ExpressionEvaluates program size_condition_evaluates context evidence source
          environment before condition (.bool true) conditionHeap)
        (fault : StatementsFault program size_fault context evidence source environment
          conditionHeap body finalContext reason after) :
        WhileFaults program (stepSize [size_condition_evaluates, size_fault]) context evidence source environment before condition
          body reason after
    | nextFallthrough
        {size_condition_evaluates size_body_executes size_fault : Nat}
        {context evidence source environment before conditionHeap bodyHeap after
          condition body bodyFinalContext bodyEnvironment reason}
        (condition_evaluates : ExpressionEvaluates program size_condition_evaluates context evidence source
          environment before condition (.bool true) conditionHeap)
        (body_executes : StatementsExecute program size_body_executes context evidence source environment
          conditionHeap body bodyFinalContext (.fallthrough bodyEnvironment) bodyHeap)
        (fault : WhileFaults program size_fault context evidence source environment bodyHeap
          condition body reason after) :
        WhileFaults program (stepSize [size_condition_evaluates, size_body_executes, size_fault]) context evidence source environment before condition
          body reason after
    | nextContinue
        {size_condition_evaluates size_body_executes size_fault : Nat}
        {context evidence source environment before conditionHeap bodyHeap after
          condition body bodyFinalContext bodyEnvironment reason}
        (condition_evaluates : ExpressionEvaluates program size_condition_evaluates context evidence source
          environment before condition (.bool true) conditionHeap)
        (body_executes : StatementsExecute program size_body_executes context evidence source environment
          conditionHeap body bodyFinalContext (.continuing bodyEnvironment) bodyHeap)
        (fault : WhileFaults program size_fault context evidence source environment bodyHeap
          condition body reason after) :
        WhileFaults program (stepSize [size_condition_evaluates, size_body_executes, size_fault]) context evidence source environment before condition
          body reason after

  inductive ForLoopFaults (program : Program) : Nat →
      Context → EvidenceEnvironment → TypedSource → Dynamic.Environment → Heap →
        ExpressionId → List ForItemForm → List StatementId → SemanticFault →
        Heap → Prop where
    | condition
        {size_fault : Nat}
        {context evidence source environment before after condition post body reason}
        (fault : ExpressionFaults program size_fault context evidence source environment
          before condition reason after) :
        ForLoopFaults program (stepSize [size_fault]) context evidence source environment before condition
          post body reason after
    | conditionType
        {size_evaluate : Nat}
        {context evidence source environment before after condition post body value
          actual}
        (evaluate : ExpressionEvaluates program size_evaluate context evidence source environment
          before condition value after)
        (not_boolean : ¬ BooleanValue value)
        (actual_type : ValueRuntimeType value actual) :
        ForLoopFaults program (stepSize [size_evaluate]) context evidence source environment before condition
          post body (.typeMismatch .bool actual) after
    | body
        {size_condition_evaluates size_fault : Nat}
        {context evidence source environment before conditionHeap after condition
          post body finalContext reason}
        (condition_evaluates : ExpressionEvaluates program size_condition_evaluates context evidence source
          environment before condition (.bool true) conditionHeap)
        (fault : StatementsFault program size_fault context evidence source environment
          conditionHeap body finalContext reason after) :
        ForLoopFaults program (stepSize [size_condition_evaluates, size_fault]) context evidence source environment before condition
          post body reason after
    | postFallthrough
        {size_condition_evaluates size_body_executes size_fault : Nat}
        {context evidence source environment before conditionHeap bodyHeap after
          condition post body bodyFinalContext bodyEnvironment finalContext reason}
        (condition_evaluates : ExpressionEvaluates program size_condition_evaluates context evidence source
          environment before condition (.bool true) conditionHeap)
        (body_executes : StatementsExecute program size_body_executes context evidence source environment
          conditionHeap body bodyFinalContext (.fallthrough bodyEnvironment) bodyHeap)
        (fault : ForItemsFault program size_fault context evidence source environment bodyHeap
          post finalContext reason after) :
        ForLoopFaults program (stepSize [size_condition_evaluates, size_body_executes, size_fault]) context evidence source environment before condition
          post body reason after
    | postContinue
        {size_condition_evaluates size_body_executes size_fault : Nat}
        {context evidence source environment before conditionHeap bodyHeap after
          condition post body bodyFinalContext bodyEnvironment finalContext reason}
        (condition_evaluates : ExpressionEvaluates program size_condition_evaluates context evidence source
          environment before condition (.bool true) conditionHeap)
        (body_executes : StatementsExecute program size_body_executes context evidence source environment
          conditionHeap body bodyFinalContext (.continuing bodyEnvironment) bodyHeap)
        (fault : ForItemsFault program size_fault context evidence source environment bodyHeap
          post finalContext reason after) :
        ForLoopFaults program (stepSize [size_condition_evaluates, size_body_executes, size_fault]) context evidence source environment before condition
          post body reason after
    | nextFallthrough
        {size_condition_evaluates size_body_executes size_post_executes size_fault : Nat}
        {context evidence source environment before conditionHeap bodyHeap postHeap
          after condition post body bodyFinalContext postFinalContext bodyEnvironment
          postEnvironment reason}
        (condition_evaluates : ExpressionEvaluates program size_condition_evaluates context evidence source
          environment before condition (.bool true) conditionHeap)
        (body_executes : StatementsExecute program size_body_executes context evidence source environment
          conditionHeap body bodyFinalContext (.fallthrough bodyEnvironment) bodyHeap)
        (post_executes : ForItemsExecute program size_post_executes context evidence source environment
          bodyHeap post postFinalContext postEnvironment postHeap)
        (fault : ForLoopFaults program size_fault context evidence source environment postHeap
          condition post body reason after) :
        ForLoopFaults program (stepSize [size_condition_evaluates, size_body_executes, size_post_executes, size_fault]) context evidence source environment before condition
          post body reason after
    | nextContinue
        {size_condition_evaluates size_body_executes size_post_executes size_fault : Nat}
        {context evidence source environment before conditionHeap bodyHeap postHeap
          after condition post body bodyFinalContext postFinalContext bodyEnvironment
          postEnvironment reason}
        (condition_evaluates : ExpressionEvaluates program size_condition_evaluates context evidence source
          environment before condition (.bool true) conditionHeap)
        (body_executes : StatementsExecute program size_body_executes context evidence source environment
          conditionHeap body bodyFinalContext (.continuing bodyEnvironment) bodyHeap)
        (post_executes : ForItemsExecute program size_post_executes context evidence source environment
          bodyHeap post postFinalContext postEnvironment postHeap)
        (fault : ForLoopFaults program size_fault context evidence source environment postHeap
          condition post body reason after) :
        ForLoopFaults program (stepSize [size_condition_evaluates, size_body_executes, size_post_executes, size_fault]) context evidence source environment before condition
          post body reason after

end

mutual
theorem ExpressionFaults.sound {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : ExpressionId} {a6 : SemanticFault} {a7 : Heap}
    (trace : ExpressionFaults program size a0 a1 a2 a3 a4 a5 a6 a7) : Dynamic.ExpressionFaults program a0 a1 a2 a3 a4 a5 a6 a7 := by
  match trace with
  | .missing absent =>
    exact .missing absent
  | .form contains fault =>
    exact .form contains (ExpressionFormFaults.sound fault)
  | .coercion contains form fault =>
    exact .coercion contains (ExpressionFormEvaluates.sound form) (CoercionPathFaults.sound fault)
  | .generalizedLocalRequirement contains form_eq layout lookup read descriptor context_fields selection fault =>
    exact .generalizedLocalRequirement contains form_eq layout lookup read descriptor context_fields selection fault
  | .generalizedLocalCoercion contains form_eq layout lookup read descriptor context_fields instantiation fault =>
    exact .generalizedLocalCoercion contains form_eq layout lookup read descriptor context_fields instantiation (CoercionPathFaults.sound fault)
termination_by structural trace

theorem ExpressionFormFaults.sound {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : ExpressionForm} {a6 : List RequirementId} {a7 : List CoercionStep} {a8 : SemanticFault} {a9 : Heap}
    (trace : ExpressionFormFaults program size a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) : Dynamic.ExpressionFormFaults program a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 := by
  match trace with
  | .integerRequirement layout fault =>
    exact .integerRequirement layout fault
  | .localUnbound layout unbound =>
    exact .localUnbound layout unbound
  | .localDangling layout lookup dangling =>
    exact .localDangling layout lookup dangling
  | .localUninitialized layout lookup read descriptor_empty empty not_mapping =>
    exact .localUninitialized layout lookup read descriptor_empty empty not_mapping
  | .declarationRequirement layout fault =>
    exact .declarationRequirement layout fault
  | .group layout fault =>
    exact .group layout (ExpressionFaults.sound fault)
  | .tuple layout fault =>
    exact .tuple layout (ExpressionsFault.sound fault)
  | .unaryOperand layout fault =>
    exact .unaryOperand layout (ExpressionFaults.sound fault)
  | .unaryApply layout operand_evaluates fault =>
    exact .unaryApply layout (ExpressionEvaluates.sound operand_evaluates) (UnaryOperationFaults.sound fault)
  | .binaryLeft layout fault =>
    exact .binaryLeft layout (ExpressionFaults.sound fault)
  | .binaryLeftOperand layout left_evaluates invalid =>
    exact .binaryLeftOperand layout (ExpressionEvaluates.sound left_evaluates) invalid
  | .binaryRight layout left_evaluates evaluate_right fault =>
    exact .binaryRight layout (ExpressionEvaluates.sound left_evaluates) evaluate_right (ExpressionFaults.sound fault)
  | .binaryApply layout left_evaluates evaluate_right right_evaluates fault =>
    exact .binaryApply layout (ExpressionEvaluates.sound left_evaluates) evaluate_right (ExpressionEvaluates.sound right_evaluates) (BinaryOperationFaults.sound fault)
  | .conditionalCondition layout fault =>
    exact .conditionalCondition layout (ExpressionFaults.sound fault)
  | .conditionalType layout condition_evaluates not_boolean actual_type =>
    exact .conditionalType layout (ExpressionEvaluates.sound condition_evaluates) not_boolean actual_type
  | .conditionalTrueBranch layout condition_evaluates fault =>
    exact .conditionalTrueBranch layout (ExpressionEvaluates.sound condition_evaluates) (ExpressionFaults.sound fault)
  | .conditionalFalseBranch layout condition_evaluates fault =>
    exact .conditionalFalseBranch layout (ExpressionEvaluates.sound condition_evaluates) (ExpressionFaults.sound fault)
  | .directCalleeMissing absent =>
    exact .directCalleeMissing absent
  | .directArguments callee_contains callee_form fault =>
    exact .directArguments callee_contains callee_form (ExpressionsFault.sound fault)
  | .directRequirements arguments_evaluate fault =>
    exact .directRequirements (ExpressionsEvaluate.sound arguments_evaluate) fault
  | .directApply arguments_evaluate call_evidence fault =>
    exact .directApply (ExpressionsEvaluate.sound arguments_evaluate) call_evidence (CallableFaults.sound fault)
  | .builtinArguments layout fault =>
    exact .builtinArguments layout (ExpressionsFault.sound fault)
  | .builtinApply layout arguments_evaluate fault =>
    exact .builtinApply layout (ExpressionsEvaluate.sound arguments_evaluate) (CallableFaults.sound fault)
  | .indirectCallee fault =>
    exact .indirectCallee (ExpressionFaults.sound fault)
  | .indirectNotCallable callee_evaluates not_callable =>
    exact .indirectNotCallable (ExpressionEvaluates.sound callee_evaluates) not_callable
  | .indirectArguments callee_evaluates callable_shape fault =>
    exact .indirectArguments (ExpressionEvaluates.sound callee_evaluates) callable_shape (ExpressionsFault.sound fault)
  | .indirectSourceArity callee_evaluates arguments_evaluate mismatch =>
    exact .indirectSourceArity (ExpressionEvaluates.sound callee_evaluates) (ExpressionsEvaluate.sound arguments_evaluate) mismatch
  | .indirectArgumentCoercion callee_evaluates arguments_evaluate source_arity pack fault =>
    exact .indirectArgumentCoercion (ExpressionEvaluates.sound callee_evaluates) (ExpressionsEvaluate.sound arguments_evaluate) source_arity pack (CoercionPathFaults.sound fault)
  | .indirectApply callee_evaluates arguments_evaluate pack_before argument_coercions pack_after source_arity applied_arity fault =>
    exact .indirectApply (ExpressionEvaluates.sound callee_evaluates) (ExpressionsEvaluate.sound arguments_evaluate) pack_before (CoercionPathExecutes.sound argument_coercions) pack_after source_arity applied_arity (CallableFaults.sound fault)
  | .constructorArgument layout fault =>
    exact .constructorArgument layout (ExpressionsFault.sound fault)
  | .constructorMetadata layout fault =>
    exact .constructorMetadata layout fault
  | .memberBase layout fault =>
    exact .memberBase layout (ExpressionFaults.sound fault)
  | .memberShape layout base_evaluates not_constructed =>
    exact .memberShape layout (ExpressionEvaluates.sound base_evaluates) not_constructed
  | .memberIndex layout base_evaluates missing =>
    exact .memberIndex layout (ExpressionEvaluates.sound base_evaluates) missing
  | .indexBase layout fault =>
    exact .indexBase layout (ExpressionFaults.sound fault)
  | .indexKey layout base_evaluates fault =>
    exact .indexKey layout (ExpressionEvaluates.sound base_evaluates) (ExpressionFaults.sound fault)
  | .indexShape layout base_evaluates index_evaluates not_mapping =>
    exact .indexShape layout (ExpressionEvaluates.sound base_evaluates) (ExpressionEvaluates.sound index_evaluates) not_mapping
  | .indexKeyType layout base_evaluates index_evaluates actual_type mismatch =>
    exact .indexKeyType layout (ExpressionEvaluates.sound base_evaluates) (ExpressionEvaluates.sound index_evaluates) actual_type mismatch
  | .indexDefaultUnavailable layout base_evaluates index_evaluates key_type absent not_defaultable =>
    exact .indexDefaultUnavailable layout (ExpressionEvaluates.sound base_evaluates) (ExpressionEvaluates.sound index_evaluates) key_type absent not_defaultable
termination_by structural trace

theorem ExpressionsFault.sound {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : List ExpressionId} {a6 : SemanticFault} {a7 : Heap}
    (trace : ExpressionsFault program size a0 a1 a2 a3 a4 a5 a6 a7) : Dynamic.ExpressionsFault program a0 a1 a2 a3 a4 a5 a6 a7 := by
  match trace with
  | .head fault =>
    exact .head (ExpressionFaults.sound fault)
  | .tail head fault =>
    exact .tail (ExpressionEvaluates.sound head) (ExpressionsFault.sound fault)
termination_by structural trace

theorem UnaryOperationFaults.sound {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : Heap} {a3 : Syntax.UnaryOp} {a4 : List RequirementId} {a5 : Value} {a6 : SemanticFault} {a7 : Heap}
    (trace : UnaryOperationFaults program size a0 a1 a2 a3 a4 a5 a6 a7) : Dynamic.UnaryOperationFaults program a0 a1 a2 a3 a4 a5 a6 a7 := by
  match trace with
  | .primitive invalid =>
    exact .primitive invalid
  | .requirement fault =>
    exact .requirement fault
  | .method dispatch selected fault =>
    exact .method dispatch selected (BodyFaults.sound fault)
termination_by structural trace

theorem BinaryOperationFaults.sound {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : Heap} {a3 : Syntax.BinaryOp} {a4 : List RequirementId} {a5 : Value} {a6 : Value} {a7 : SemanticFault} {a8 : Heap}
    (trace : BinaryOperationFaults program size a0 a1 a2 a3 a4 a5 a6 a7 a8) : Dynamic.BinaryOperationFaults program a0 a1 a2 a3 a4 a5 a6 a7 a8 := by
  match trace with
  | .primitive invalid =>
    exact .primitive invalid
  | .requirement fault =>
    exact .requirement fault
  | .method dispatch selected fault =>
    exact .method dispatch selected (BodyFaults.sound fault)
termination_by structural trace

theorem CoercionStepFaults.sound {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : Heap} {a3 : CoercionStep} {a4 : Value} {a5 : SemanticFault} {a6 : Heap}
    (trace : CoercionStepFaults program size a0 a1 a2 a3 a4 a5 a6) : Dynamic.CoercionStepFaults program a0 a1 a2 a3 a4 a5 a6 := by
  match trace with
  | .requirement fault =>
    exact .requirement fault
  | .primitiveInput no_source_method invalid actual_type =>
    exact .primitiveInput no_source_method invalid actual_type
  | .method selected fault =>
    exact .method selected (BodyFaults.sound fault)
termination_by structural trace

theorem CoercionPathFaults.sound {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : Heap} {a3 : List CoercionStep} {a4 : Value} {a5 : SemanticFault} {a6 : Heap}
    (trace : CoercionPathFaults program size a0 a1 a2 a3 a4 a5 a6) : Dynamic.CoercionPathFaults program a0 a1 a2 a3 a4 a5 a6 := by
  match trace with
  | .head fault =>
    exact .head (CoercionStepFaults.sound fault)
  | .tail head fault =>
    exact .tail (CoercionStepExecutes.sound head) (CoercionPathFaults.sound fault)
termination_by structural trace

theorem CallableFaults.sound {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : EvidenceEnvironment} {a3 : Heap} {a4 : Value} {a5 : List Value} {a6 : SemanticFault} {a7 : Heap}
    (trace : CallableFaults program size a0 a1 a2 a3 a4 a5 a6 a7) : Dynamic.CallableFaults program a0 a1 a2 a3 a4 a5 a6 a7 := by
  match trace with
  | .notCallable invalid =>
    exact .notCallable invalid
  | .builtinArity mismatch =>
    exact .builtinArity mismatch
  | .builtinArgumentType arity mismatch =>
    exact .builtinArgumentType arity mismatch
  | .globalSignatureMissing missing =>
    exact .globalSignatureMissing missing
  | .globalBodyMissing missing =>
    exact .globalBodyMissing missing
  | .globalArity instantiates mismatch =>
    exact .globalArity instantiates mismatch
  | .globalBody instantiates invocation_eq fault =>
    exact .globalBody instantiates invocation_eq (BodyFaults.sound fault)
  | .closureArity mismatch =>
    exact .closureArity mismatch
  | .closureBody invocation_eq frame parameters_extend allocate fault =>
    exact .closureBody invocation_eq frame parameters_extend allocate (FunctionStatementsFault.sound fault)
  | .closureControlEscape invocation_eq frame parameters_extend allocate execute escaped =>
    exact .closureControlEscape invocation_eq frame parameters_extend allocate (FunctionStatementsExecute.sound execute) escaped
termination_by structural trace

theorem BodyFaults.sound {program : Program} {size : Nat} {a0 : BodyInstance} {a1 : EvidenceEnvironment} {a2 : Heap} {a3 : List Value} {a4 : SemanticFault} {a5 : Heap}
    (trace : BodyFaults program size a0 a1 a2 a3 a4 a5) : Dynamic.BodyFaults program a0 a1 a2 a3 a4 a5 := by
  match trace with
  | .arity mismatch =>
    exact .arity mismatch
  | .statements roots_eq inputs_extend allocate fault =>
    exact .statements roots_eq inputs_extend allocate (FunctionStatementsFault.sound fault)
  | .controlEscape roots_eq inputs_extend allocate execute escaped =>
    exact .controlEscape roots_eq inputs_extend allocate (FunctionStatementsExecute.sound execute) escaped
termination_by structural trace

theorem StatementFaults.sound {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : StatementId} {a6 : SemanticFault} {a7 : Heap}
    (trace : StatementFaults program size a0 a1 a2 a3 a4 a5 a6 a7) : Dynamic.StatementFaults program a0 a1 a2 a3 a4 a5 a6 a7 := by
  match trace with
  | .missing absent =>
    exact .missing absent
  | .polymorphicLet contains form_eq polymorphic unsupported =>
    exact .polymorphicLet contains form_eq polymorphic unsupported
  | .letInitializer contains form_eq monomorphic fault =>
    exact .letInitializer contains form_eq monomorphic (ExpressionFaults.sound fault)
  | .returnValue contains form_eq fault =>
    exact .returnValue contains form_eq (ExpressionFaults.sound fault)
  | .expression contains form_eq fault =>
    exact .expression contains form_eq (ExpressionFaults.sound fault)
  | .assignValue contains form_eq fault =>
    exact .assignValue contains form_eq (SourcePlaceAssignmentFaults.sound fault)
  | .assignBitNot contains form_eq fault =>
    exact .assignBitNot contains form_eq (SourcePlaceBitNotFaults.sound fault)
  | .ifCondition contains form_eq fault =>
    exact .ifCondition contains form_eq (ExpressionFaults.sound fault)
  | .ifConditionType contains form_eq evaluate not_boolean actual_type =>
    exact .ifConditionType contains form_eq (ExpressionEvaluates.sound evaluate) not_boolean actual_type
  | .ifTrueBody contains form_eq evaluate fault =>
    exact .ifTrueBody contains form_eq (ExpressionEvaluates.sound evaluate) (StatementsFault.sound fault)
  | .ifFalseBody contains form_eq evaluate fault =>
    exact .ifFalseBody contains form_eq (ExpressionEvaluates.sound evaluate) (StatementsFault.sound fault)
  | .block contains form_eq fault =>
    exact .block contains form_eq (StatementsFault.sound fault)
  | .matchScrutinee contains form_eq fault =>
    exact .matchScrutinee contains form_eq (ExpressionFaults.sound fault)
  | .matchPattern contains form_eq scrutinee_contains scrutinee_evaluates allocate_hidden fault =>
    exact .matchPattern contains form_eq scrutinee_contains (ExpressionEvaluates.sound scrutinee_evaluates) allocate_hidden fault
  | .matchArmBody contains form_eq scrutinee_contains scrutinee_evaluates allocate_hidden select binders_eq values_eq binders_extend allocate_bindings fault =>
    exact .matchArmBody contains form_eq scrutinee_contains (ExpressionEvaluates.sound scrutinee_evaluates) allocate_hidden select binders_eq values_eq binders_extend allocate_bindings (StatementsFault.sound fault)
  | .matchDefaultBody contains form_eq scrutinee_contains scrutinee_evaluates allocate_hidden select fault =>
    exact .matchDefaultBody contains form_eq scrutinee_contains (ExpressionEvaluates.sound scrutinee_evaluates) allocate_hidden select (StatementsFault.sound fault)
  | .forInitializer contains form_eq fault =>
    exact .forInitializer contains form_eq (ForItemsFault.sound fault)
  | .forIteration contains form_eq initializer_executes fault =>
    exact .forIteration contains form_eq (ForItemsExecute.sound initializer_executes) (ForLoopFaults.sound fault)
  | .whileIteration contains form_eq fault =>
    exact .whileIteration contains form_eq (WhileFaults.sound fault)
termination_by structural trace

theorem StatementsFault.sound {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : List StatementId} {a6 : Context} {a7 : SemanticFault} {a8 : Heap}
    (trace : StatementsFault program size a0 a1 a2 a3 a4 a5 a6 a7 a8) : Dynamic.StatementsFault program a0 a1 a2 a3 a4 a5 a6 a7 a8 := by
  match trace with
  | .head fault =>
    exact .head (StatementFaults.sound fault)
  | .tail head fault =>
    exact .tail (StatementExecutes.sound head) (StatementsFault.sound fault)
termination_by structural trace

theorem FunctionStatementsFault.sound {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : List StatementId} {a6 : Context} {a7 : SemanticFault} {a8 : Heap}
    (trace : FunctionStatementsFault program size a0 a1 a2 a3 a4 a5 a6 a7 a8) : Dynamic.FunctionStatementsFault program a0 a1 a2 a3 a4 a5 a6 a7 a8 := by
  match trace with
  | .singleton fault =>
    exact .singleton (StatementFaults.sound fault)
  | .tailExpression contains form_eq fault =>
    exact .tailExpression contains form_eq (ExpressionFaults.sound fault)
  | .head fault =>
    exact .head (StatementFaults.sound fault)
  | .tail head fault =>
    exact .tail (StatementExecutes.sound head) (FunctionStatementsFault.sound fault)
termination_by structural trace

theorem SourcePlaceFaults.sound {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : PlaceResolution} {a6 : SemanticFault} {a7 : Heap}
    (trace : SourcePlaceFaults program size a0 a1 a2 a3 a4 a5 a6 a7) : Dynamic.SourcePlaceFaults program a0 a1 a2 a3 a4 a5 a6 a7 := by
  match trace with
  | .unbound missing =>
    exact .unbound missing
  | .dangling lookup missing =>
    exact .dangling lookup missing
  | .projectionExpression lookup read fault =>
    exact .projectionExpression lookup read (SourceProjectionsFault.sound fault)
  | .danglingAfterProjections lookup read evaluate missing =>
    exact .danglingAfterProjections lookup read (SourceProjectionsEvaluate.sound evaluate) missing
  | .projectionRead lookup initial_read evaluate current_read initial_value fault =>
    exact .projectionRead lookup initial_read (SourceProjectionsEvaluate.sound evaluate) current_read initial_value fault
  | .uninitialized lookup initial_read evaluate current_read empty not_mapping has_projection =>
    exact .uninitialized lookup initial_read (SourceProjectionsEvaluate.sound evaluate) current_read empty not_mapping has_projection
termination_by structural trace

theorem SourceProjectionsFault.sound {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : List PlaceProjection} {a6 : SemanticFault} {a7 : Heap}
    (trace : SourceProjectionsFault program size a0 a1 a2 a3 a4 a5 a6 a7) : Dynamic.SourceProjectionsFault program a0 a1 a2 a3 a4 a5 a6 a7 := by
  match trace with
  | .indexHead fault =>
    exact .indexHead (ExpressionFaults.sound fault)
  | .indexTail head fault =>
    exact .indexTail (ExpressionEvaluates.sound head) (SourceProjectionsFault.sound fault)
  | .memberTail fault =>
    exact .memberTail (SourceProjectionsFault.sound fault)
termination_by structural trace

theorem SourcePlaceAssignmentFaults.sound {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : PlaceResolution} {a6 : Syntax.ValueAssignOp} {a7 : ExpressionId} {a8 : SemanticFault} {a9 : Heap}
    (trace : SourcePlaceAssignmentFaults program size a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) : Dynamic.SourcePlaceAssignmentFaults program a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 := by
  match trace with
  | .target fault =>
    exact .target (SourcePlaceFaults.sound fault)
  | .rhs resolve fault =>
    exact .rhs (SourcePlaceResolves.sound resolve) (ExpressionFaults.sound fault)
  | .operands resolve evaluate current_read root_type_eq initial_value path_read invalid =>
    exact .operands (SourcePlaceResolves.sound resolve) (ExpressionEvaluates.sound evaluate) current_read root_type_eq initial_value path_read invalid
  | .structuralUpdate resolve evaluate current_read root_type_eq initial_value fault =>
    exact .structuralUpdate (SourcePlaceResolves.sound resolve) (ExpressionEvaluates.sound evaluate) current_read root_type_eq initial_value fault
termination_by structural trace

theorem SourcePlaceBitNotFaults.sound {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : PlaceResolution} {a6 : SemanticFault} {a7 : Heap}
    (trace : SourcePlaceBitNotFaults program size a0 a1 a2 a3 a4 a5 a6 a7) : Dynamic.SourcePlaceBitNotFaults program a0 a1 a2 a3 a4 a5 a6 a7 := by
  match trace with
  | .target fault =>
    exact .target (SourcePlaceFaults.sound fault)
  | .uninitialized resolve empty =>
    exact .uninitialized (SourcePlaceResolves.sound resolve) empty
  | .operand resolve selected invalid =>
    exact .operand (SourcePlaceResolves.sound resolve) selected invalid
termination_by structural trace

theorem ForItemFaults.sound {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : ForItemForm} {a6 : SemanticFault} {a7 : Heap}
    (trace : ForItemFaults program size a0 a1 a2 a3 a4 a5 a6 a7) : Dynamic.ForItemFaults program a0 a1 a2 a3 a4 a5 a6 a7 := by
  match trace with
  | .polymorphicLet polymorphic unsupported =>
    exact .polymorphicLet polymorphic unsupported
  | .letInitializer monomorphic fault =>
    exact .letInitializer monomorphic (ExpressionFaults.sound fault)
  | .expression fault =>
    exact .expression (ExpressionFaults.sound fault)
  | .assignValue fault =>
    exact .assignValue (SourcePlaceAssignmentFaults.sound fault)
  | .assignBitNot fault =>
    exact .assignBitNot (SourcePlaceBitNotFaults.sound fault)
termination_by structural trace

theorem ForItemsFault.sound {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : List ForItemForm} {a6 : Context} {a7 : SemanticFault} {a8 : Heap}
    (trace : ForItemsFault program size a0 a1 a2 a3 a4 a5 a6 a7 a8) : Dynamic.ForItemsFault program a0 a1 a2 a3 a4 a5 a6 a7 a8 := by
  match trace with
  | .head fault =>
    exact .head (ForItemFaults.sound fault)
  | .tail head fault =>
    exact .tail (ForItemExecutes.sound head) (ForItemsFault.sound fault)
termination_by structural trace

theorem WhileFaults.sound {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : ExpressionId} {a6 : List StatementId} {a7 : SemanticFault} {a8 : Heap}
    (trace : WhileFaults program size a0 a1 a2 a3 a4 a5 a6 a7 a8) : Dynamic.WhileFaults program a0 a1 a2 a3 a4 a5 a6 a7 a8 := by
  match trace with
  | .condition fault =>
    exact .condition (ExpressionFaults.sound fault)
  | .conditionType evaluate not_boolean actual_type =>
    exact .conditionType (ExpressionEvaluates.sound evaluate) not_boolean actual_type
  | .body condition_evaluates fault =>
    exact .body (ExpressionEvaluates.sound condition_evaluates) (StatementsFault.sound fault)
  | .nextFallthrough condition_evaluates body_executes fault =>
    exact .nextFallthrough (ExpressionEvaluates.sound condition_evaluates) (StatementsExecute.sound body_executes) (WhileFaults.sound fault)
  | .nextContinue condition_evaluates body_executes fault =>
    exact .nextContinue (ExpressionEvaluates.sound condition_evaluates) (StatementsExecute.sound body_executes) (WhileFaults.sound fault)
termination_by structural trace

theorem ForLoopFaults.sound {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : ExpressionId} {a6 : List ForItemForm} {a7 : List StatementId} {a8 : SemanticFault} {a9 : Heap}
    (trace : ForLoopFaults program size a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) : Dynamic.ForLoopFaults program a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 := by
  match trace with
  | .condition fault =>
    exact .condition (ExpressionFaults.sound fault)
  | .conditionType evaluate not_boolean actual_type =>
    exact .conditionType (ExpressionEvaluates.sound evaluate) not_boolean actual_type
  | .body condition_evaluates fault =>
    exact .body (ExpressionEvaluates.sound condition_evaluates) (StatementsFault.sound fault)
  | .postFallthrough condition_evaluates body_executes fault =>
    exact .postFallthrough (ExpressionEvaluates.sound condition_evaluates) (StatementsExecute.sound body_executes) (ForItemsFault.sound fault)
  | .postContinue condition_evaluates body_executes fault =>
    exact .postContinue (ExpressionEvaluates.sound condition_evaluates) (StatementsExecute.sound body_executes) (ForItemsFault.sound fault)
  | .nextFallthrough condition_evaluates body_executes post_executes fault =>
    exact .nextFallthrough (ExpressionEvaluates.sound condition_evaluates) (StatementsExecute.sound body_executes) (ForItemsExecute.sound post_executes) (ForLoopFaults.sound fault)
  | .nextContinue condition_evaluates body_executes post_executes fault =>
    exact .nextContinue (ExpressionEvaluates.sound condition_evaluates) (StatementsExecute.sound body_executes) (ForItemsExecute.sound post_executes) (ForLoopFaults.sound fault)
termination_by structural trace

end

mutual
theorem ExpressionFaults.has_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : ExpressionId} {a6 : SemanticFault} {a7 : Heap}
    (trace : Dynamic.ExpressionFaults program a0 a1 a2 a3 a4 a5 a6 a7) : ∃ size, ExpressionFaults program size a0 a1 a2 a3 a4 a5 a6 a7 := by
  match trace with
  | .missing absent =>
    exact ⟨_, .missing absent⟩
  | .form contains fault =>
    obtain ⟨size_fault, fault⟩ := ExpressionFormFaults.has_size fault
    exact ⟨_, .form contains fault⟩
  | .coercion contains form fault =>
    obtain ⟨size_form, form⟩ := ExpressionFormEvaluates.has_size form
    obtain ⟨size_fault, fault⟩ := CoercionPathFaults.has_size fault
    exact ⟨_, .coercion contains form fault⟩
  | .generalizedLocalRequirement contains form_eq layout lookup read descriptor context_fields selection fault =>
    exact ⟨_, .generalizedLocalRequirement contains form_eq layout lookup read descriptor context_fields selection fault⟩
  | .generalizedLocalCoercion contains form_eq layout lookup read descriptor context_fields instantiation fault =>
    obtain ⟨size_fault, fault⟩ := CoercionPathFaults.has_size fault
    exact ⟨_, .generalizedLocalCoercion contains form_eq layout lookup read descriptor context_fields instantiation fault⟩
termination_by structural trace

theorem ExpressionFormFaults.has_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : ExpressionForm} {a6 : List RequirementId} {a7 : List CoercionStep} {a8 : SemanticFault} {a9 : Heap}
    (trace : Dynamic.ExpressionFormFaults program a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) : ∃ size, ExpressionFormFaults program size a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 := by
  match trace with
  | .integerRequirement layout fault =>
    exact ⟨_, .integerRequirement layout fault⟩
  | .localUnbound layout unbound =>
    exact ⟨_, .localUnbound layout unbound⟩
  | .localDangling layout lookup dangling =>
    exact ⟨_, .localDangling layout lookup dangling⟩
  | .localUninitialized layout lookup read descriptor_empty empty not_mapping =>
    exact ⟨_, .localUninitialized layout lookup read descriptor_empty empty not_mapping⟩
  | .declarationRequirement layout fault =>
    exact ⟨_, .declarationRequirement layout fault⟩
  | .group layout fault =>
    obtain ⟨size_fault, fault⟩ := ExpressionFaults.has_size fault
    exact ⟨_, .group layout fault⟩
  | .tuple layout fault =>
    obtain ⟨size_fault, fault⟩ := ExpressionsFault.has_size fault
    exact ⟨_, .tuple layout fault⟩
  | .unaryOperand layout fault =>
    obtain ⟨size_fault, fault⟩ := ExpressionFaults.has_size fault
    exact ⟨_, .unaryOperand layout fault⟩
  | .unaryApply layout operand_evaluates fault =>
    obtain ⟨size_operand_evaluates, operand_evaluates⟩ := ExpressionEvaluates.has_size operand_evaluates
    obtain ⟨size_fault, fault⟩ := UnaryOperationFaults.has_size fault
    exact ⟨_, .unaryApply layout operand_evaluates fault⟩
  | .binaryLeft layout fault =>
    obtain ⟨size_fault, fault⟩ := ExpressionFaults.has_size fault
    exact ⟨_, .binaryLeft layout fault⟩
  | .binaryLeftOperand layout left_evaluates invalid =>
    obtain ⟨size_left_evaluates, left_evaluates⟩ := ExpressionEvaluates.has_size left_evaluates
    exact ⟨_, .binaryLeftOperand layout left_evaluates invalid⟩
  | .binaryRight layout left_evaluates evaluate_right fault =>
    obtain ⟨size_left_evaluates, left_evaluates⟩ := ExpressionEvaluates.has_size left_evaluates
    obtain ⟨size_fault, fault⟩ := ExpressionFaults.has_size fault
    exact ⟨_, .binaryRight layout left_evaluates evaluate_right fault⟩
  | .binaryApply layout left_evaluates evaluate_right right_evaluates fault =>
    obtain ⟨size_left_evaluates, left_evaluates⟩ := ExpressionEvaluates.has_size left_evaluates
    obtain ⟨size_right_evaluates, right_evaluates⟩ := ExpressionEvaluates.has_size right_evaluates
    obtain ⟨size_fault, fault⟩ := BinaryOperationFaults.has_size fault
    exact ⟨_, .binaryApply layout left_evaluates evaluate_right right_evaluates fault⟩
  | .conditionalCondition layout fault =>
    obtain ⟨size_fault, fault⟩ := ExpressionFaults.has_size fault
    exact ⟨_, .conditionalCondition layout fault⟩
  | .conditionalType layout condition_evaluates not_boolean actual_type =>
    obtain ⟨size_condition_evaluates, condition_evaluates⟩ := ExpressionEvaluates.has_size condition_evaluates
    exact ⟨_, .conditionalType layout condition_evaluates not_boolean actual_type⟩
  | .conditionalTrueBranch layout condition_evaluates fault =>
    obtain ⟨size_condition_evaluates, condition_evaluates⟩ := ExpressionEvaluates.has_size condition_evaluates
    obtain ⟨size_fault, fault⟩ := ExpressionFaults.has_size fault
    exact ⟨_, .conditionalTrueBranch layout condition_evaluates fault⟩
  | .conditionalFalseBranch layout condition_evaluates fault =>
    obtain ⟨size_condition_evaluates, condition_evaluates⟩ := ExpressionEvaluates.has_size condition_evaluates
    obtain ⟨size_fault, fault⟩ := ExpressionFaults.has_size fault
    exact ⟨_, .conditionalFalseBranch layout condition_evaluates fault⟩
  | .directCalleeMissing absent =>
    exact ⟨_, .directCalleeMissing absent⟩
  | .directArguments callee_contains callee_form fault =>
    obtain ⟨size_fault, fault⟩ := ExpressionsFault.has_size fault
    exact ⟨_, .directArguments callee_contains callee_form fault⟩
  | .directRequirements arguments_evaluate fault =>
    obtain ⟨size_arguments_evaluate, arguments_evaluate⟩ := ExpressionsEvaluate.has_size arguments_evaluate
    exact ⟨_, .directRequirements arguments_evaluate fault⟩
  | .directApply arguments_evaluate call_evidence fault =>
    obtain ⟨size_arguments_evaluate, arguments_evaluate⟩ := ExpressionsEvaluate.has_size arguments_evaluate
    obtain ⟨size_fault, fault⟩ := CallableFaults.has_size fault
    exact ⟨_, .directApply arguments_evaluate call_evidence fault⟩
  | .builtinArguments layout fault =>
    obtain ⟨size_fault, fault⟩ := ExpressionsFault.has_size fault
    exact ⟨_, .builtinArguments layout fault⟩
  | .builtinApply layout arguments_evaluate fault =>
    obtain ⟨size_arguments_evaluate, arguments_evaluate⟩ := ExpressionsEvaluate.has_size arguments_evaluate
    obtain ⟨size_fault, fault⟩ := CallableFaults.has_size fault
    exact ⟨_, .builtinApply layout arguments_evaluate fault⟩
  | .indirectCallee fault =>
    obtain ⟨size_fault, fault⟩ := ExpressionFaults.has_size fault
    exact ⟨_, .indirectCallee fault⟩
  | .indirectNotCallable callee_evaluates not_callable =>
    obtain ⟨size_callee_evaluates, callee_evaluates⟩ := ExpressionEvaluates.has_size callee_evaluates
    exact ⟨_, .indirectNotCallable callee_evaluates not_callable⟩
  | .indirectArguments callee_evaluates callable_shape fault =>
    obtain ⟨size_callee_evaluates, callee_evaluates⟩ := ExpressionEvaluates.has_size callee_evaluates
    obtain ⟨size_fault, fault⟩ := ExpressionsFault.has_size fault
    exact ⟨_, .indirectArguments callee_evaluates callable_shape fault⟩
  | .indirectSourceArity callee_evaluates arguments_evaluate mismatch =>
    obtain ⟨size_callee_evaluates, callee_evaluates⟩ := ExpressionEvaluates.has_size callee_evaluates
    obtain ⟨size_arguments_evaluate, arguments_evaluate⟩ := ExpressionsEvaluate.has_size arguments_evaluate
    exact ⟨_, .indirectSourceArity callee_evaluates arguments_evaluate mismatch⟩
  | .indirectArgumentCoercion callee_evaluates arguments_evaluate source_arity pack fault =>
    obtain ⟨size_callee_evaluates, callee_evaluates⟩ := ExpressionEvaluates.has_size callee_evaluates
    obtain ⟨size_arguments_evaluate, arguments_evaluate⟩ := ExpressionsEvaluate.has_size arguments_evaluate
    obtain ⟨size_fault, fault⟩ := CoercionPathFaults.has_size fault
    exact ⟨_, .indirectArgumentCoercion callee_evaluates arguments_evaluate source_arity pack fault⟩
  | .indirectApply callee_evaluates arguments_evaluate pack_before argument_coercions pack_after source_arity applied_arity fault =>
    obtain ⟨size_callee_evaluates, callee_evaluates⟩ := ExpressionEvaluates.has_size callee_evaluates
    obtain ⟨size_arguments_evaluate, arguments_evaluate⟩ := ExpressionsEvaluate.has_size arguments_evaluate
    obtain ⟨size_argument_coercions, argument_coercions⟩ := CoercionPathExecutes.has_size argument_coercions
    obtain ⟨size_fault, fault⟩ := CallableFaults.has_size fault
    exact ⟨_, .indirectApply callee_evaluates arguments_evaluate pack_before argument_coercions pack_after source_arity applied_arity fault⟩
  | .constructorArgument layout fault =>
    obtain ⟨size_fault, fault⟩ := ExpressionsFault.has_size fault
    exact ⟨_, .constructorArgument layout fault⟩
  | .constructorMetadata layout fault =>
    exact ⟨_, .constructorMetadata layout fault⟩
  | .memberBase layout fault =>
    obtain ⟨size_fault, fault⟩ := ExpressionFaults.has_size fault
    exact ⟨_, .memberBase layout fault⟩
  | .memberShape layout base_evaluates not_constructed =>
    obtain ⟨size_base_evaluates, base_evaluates⟩ := ExpressionEvaluates.has_size base_evaluates
    exact ⟨_, .memberShape layout base_evaluates not_constructed⟩
  | .memberIndex layout base_evaluates missing =>
    obtain ⟨size_base_evaluates, base_evaluates⟩ := ExpressionEvaluates.has_size base_evaluates
    exact ⟨_, .memberIndex layout base_evaluates missing⟩
  | .indexBase layout fault =>
    obtain ⟨size_fault, fault⟩ := ExpressionFaults.has_size fault
    exact ⟨_, .indexBase layout fault⟩
  | .indexKey layout base_evaluates fault =>
    obtain ⟨size_base_evaluates, base_evaluates⟩ := ExpressionEvaluates.has_size base_evaluates
    obtain ⟨size_fault, fault⟩ := ExpressionFaults.has_size fault
    exact ⟨_, .indexKey layout base_evaluates fault⟩
  | .indexShape layout base_evaluates index_evaluates not_mapping =>
    obtain ⟨size_base_evaluates, base_evaluates⟩ := ExpressionEvaluates.has_size base_evaluates
    obtain ⟨size_index_evaluates, index_evaluates⟩ := ExpressionEvaluates.has_size index_evaluates
    exact ⟨_, .indexShape layout base_evaluates index_evaluates not_mapping⟩
  | .indexKeyType layout base_evaluates index_evaluates actual_type mismatch =>
    obtain ⟨size_base_evaluates, base_evaluates⟩ := ExpressionEvaluates.has_size base_evaluates
    obtain ⟨size_index_evaluates, index_evaluates⟩ := ExpressionEvaluates.has_size index_evaluates
    exact ⟨_, .indexKeyType layout base_evaluates index_evaluates actual_type mismatch⟩
  | .indexDefaultUnavailable layout base_evaluates index_evaluates key_type absent not_defaultable =>
    obtain ⟨size_base_evaluates, base_evaluates⟩ := ExpressionEvaluates.has_size base_evaluates
    obtain ⟨size_index_evaluates, index_evaluates⟩ := ExpressionEvaluates.has_size index_evaluates
    exact ⟨_, .indexDefaultUnavailable layout base_evaluates index_evaluates key_type absent not_defaultable⟩
termination_by structural trace

theorem ExpressionsFault.has_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : List ExpressionId} {a6 : SemanticFault} {a7 : Heap}
    (trace : Dynamic.ExpressionsFault program a0 a1 a2 a3 a4 a5 a6 a7) : ∃ size, ExpressionsFault program size a0 a1 a2 a3 a4 a5 a6 a7 := by
  match trace with
  | .head fault =>
    obtain ⟨size_fault, fault⟩ := ExpressionFaults.has_size fault
    exact ⟨_, .head fault⟩
  | .tail head fault =>
    obtain ⟨size_head, head⟩ := ExpressionEvaluates.has_size head
    obtain ⟨size_fault, fault⟩ := ExpressionsFault.has_size fault
    exact ⟨_, .tail head fault⟩
termination_by structural trace

theorem UnaryOperationFaults.has_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : Heap} {a3 : Syntax.UnaryOp} {a4 : List RequirementId} {a5 : Value} {a6 : SemanticFault} {a7 : Heap}
    (trace : Dynamic.UnaryOperationFaults program a0 a1 a2 a3 a4 a5 a6 a7) : ∃ size, UnaryOperationFaults program size a0 a1 a2 a3 a4 a5 a6 a7 := by
  match trace with
  | .primitive invalid =>
    exact ⟨_, .primitive invalid⟩
  | .requirement fault =>
    exact ⟨_, .requirement fault⟩
  | .method dispatch selected fault =>
    obtain ⟨size_fault, fault⟩ := BodyFaults.has_size fault
    exact ⟨_, .method dispatch selected fault⟩
termination_by structural trace

theorem BinaryOperationFaults.has_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : Heap} {a3 : Syntax.BinaryOp} {a4 : List RequirementId} {a5 : Value} {a6 : Value} {a7 : SemanticFault} {a8 : Heap}
    (trace : Dynamic.BinaryOperationFaults program a0 a1 a2 a3 a4 a5 a6 a7 a8) : ∃ size, BinaryOperationFaults program size a0 a1 a2 a3 a4 a5 a6 a7 a8 := by
  match trace with
  | .primitive invalid =>
    exact ⟨_, .primitive invalid⟩
  | .requirement fault =>
    exact ⟨_, .requirement fault⟩
  | .method dispatch selected fault =>
    obtain ⟨size_fault, fault⟩ := BodyFaults.has_size fault
    exact ⟨_, .method dispatch selected fault⟩
termination_by structural trace

theorem CoercionStepFaults.has_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : Heap} {a3 : CoercionStep} {a4 : Value} {a5 : SemanticFault} {a6 : Heap}
    (trace : Dynamic.CoercionStepFaults program a0 a1 a2 a3 a4 a5 a6) : ∃ size, CoercionStepFaults program size a0 a1 a2 a3 a4 a5 a6 := by
  match trace with
  | .requirement fault =>
    exact ⟨_, .requirement fault⟩
  | .primitiveInput no_source_method invalid actual_type =>
    exact ⟨_, .primitiveInput no_source_method invalid actual_type⟩
  | .method selected fault =>
    obtain ⟨size_fault, fault⟩ := BodyFaults.has_size fault
    exact ⟨_, .method selected fault⟩
termination_by structural trace

theorem CoercionPathFaults.has_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : Heap} {a3 : List CoercionStep} {a4 : Value} {a5 : SemanticFault} {a6 : Heap}
    (trace : Dynamic.CoercionPathFaults program a0 a1 a2 a3 a4 a5 a6) : ∃ size, CoercionPathFaults program size a0 a1 a2 a3 a4 a5 a6 := by
  match trace with
  | .head fault =>
    obtain ⟨size_fault, fault⟩ := CoercionStepFaults.has_size fault
    exact ⟨_, .head fault⟩
  | .tail head fault =>
    obtain ⟨size_head, head⟩ := CoercionStepExecutes.has_size head
    obtain ⟨size_fault, fault⟩ := CoercionPathFaults.has_size fault
    exact ⟨_, .tail head fault⟩
termination_by structural trace

theorem CallableFaults.has_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : EvidenceEnvironment} {a3 : Heap} {a4 : Value} {a5 : List Value} {a6 : SemanticFault} {a7 : Heap}
    (trace : Dynamic.CallableFaults program a0 a1 a2 a3 a4 a5 a6 a7) : ∃ size, CallableFaults program size a0 a1 a2 a3 a4 a5 a6 a7 := by
  match trace with
  | .notCallable invalid =>
    exact ⟨_, .notCallable invalid⟩
  | .builtinArity mismatch =>
    exact ⟨_, .builtinArity mismatch⟩
  | .builtinArgumentType arity mismatch =>
    exact ⟨_, .builtinArgumentType arity mismatch⟩
  | .globalSignatureMissing missing =>
    exact ⟨_, .globalSignatureMissing missing⟩
  | .globalBodyMissing missing =>
    exact ⟨_, .globalBodyMissing missing⟩
  | .globalArity instantiates mismatch =>
    exact ⟨_, .globalArity instantiates mismatch⟩
  | .globalBody instantiates invocation_eq fault =>
    obtain ⟨size_fault, fault⟩ := BodyFaults.has_size fault
    exact ⟨_, .globalBody instantiates invocation_eq fault⟩
  | .closureArity mismatch =>
    exact ⟨_, .closureArity mismatch⟩
  | .closureBody invocation_eq frame parameters_extend allocate fault =>
    obtain ⟨size_fault, fault⟩ := FunctionStatementsFault.has_size fault
    exact ⟨_, .closureBody invocation_eq frame parameters_extend allocate fault⟩
  | .closureControlEscape invocation_eq frame parameters_extend allocate execute escaped =>
    obtain ⟨size_execute, execute⟩ := FunctionStatementsExecute.has_size execute
    exact ⟨_, .closureControlEscape invocation_eq frame parameters_extend allocate execute escaped⟩
termination_by structural trace

theorem BodyFaults.has_size {program : Program} {a0 : BodyInstance} {a1 : EvidenceEnvironment} {a2 : Heap} {a3 : List Value} {a4 : SemanticFault} {a5 : Heap}
    (trace : Dynamic.BodyFaults program a0 a1 a2 a3 a4 a5) : ∃ size, BodyFaults program size a0 a1 a2 a3 a4 a5 := by
  match trace with
  | .arity mismatch =>
    exact ⟨_, .arity mismatch⟩
  | .statements roots_eq inputs_extend allocate fault =>
    obtain ⟨size_fault, fault⟩ := FunctionStatementsFault.has_size fault
    exact ⟨_, .statements roots_eq inputs_extend allocate fault⟩
  | .controlEscape roots_eq inputs_extend allocate execute escaped =>
    obtain ⟨size_execute, execute⟩ := FunctionStatementsExecute.has_size execute
    exact ⟨_, .controlEscape roots_eq inputs_extend allocate execute escaped⟩
termination_by structural trace

theorem StatementFaults.has_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : StatementId} {a6 : SemanticFault} {a7 : Heap}
    (trace : Dynamic.StatementFaults program a0 a1 a2 a3 a4 a5 a6 a7) : ∃ size, StatementFaults program size a0 a1 a2 a3 a4 a5 a6 a7 := by
  match trace with
  | .missing absent =>
    exact ⟨_, .missing absent⟩
  | .polymorphicLet contains form_eq polymorphic unsupported =>
    exact ⟨_, .polymorphicLet contains form_eq polymorphic unsupported⟩
  | .letInitializer contains form_eq monomorphic fault =>
    obtain ⟨size_fault, fault⟩ := ExpressionFaults.has_size fault
    exact ⟨_, .letInitializer contains form_eq monomorphic fault⟩
  | .returnValue contains form_eq fault =>
    obtain ⟨size_fault, fault⟩ := ExpressionFaults.has_size fault
    exact ⟨_, .returnValue contains form_eq fault⟩
  | .expression contains form_eq fault =>
    obtain ⟨size_fault, fault⟩ := ExpressionFaults.has_size fault
    exact ⟨_, .expression contains form_eq fault⟩
  | .assignValue contains form_eq fault =>
    obtain ⟨size_fault, fault⟩ := SourcePlaceAssignmentFaults.has_size fault
    exact ⟨_, .assignValue contains form_eq fault⟩
  | .assignBitNot contains form_eq fault =>
    obtain ⟨size_fault, fault⟩ := SourcePlaceBitNotFaults.has_size fault
    exact ⟨_, .assignBitNot contains form_eq fault⟩
  | .ifCondition contains form_eq fault =>
    obtain ⟨size_fault, fault⟩ := ExpressionFaults.has_size fault
    exact ⟨_, .ifCondition contains form_eq fault⟩
  | .ifConditionType contains form_eq evaluate not_boolean actual_type =>
    obtain ⟨size_evaluate, evaluate⟩ := ExpressionEvaluates.has_size evaluate
    exact ⟨_, .ifConditionType contains form_eq evaluate not_boolean actual_type⟩
  | .ifTrueBody contains form_eq evaluate fault =>
    obtain ⟨size_evaluate, evaluate⟩ := ExpressionEvaluates.has_size evaluate
    obtain ⟨size_fault, fault⟩ := StatementsFault.has_size fault
    exact ⟨_, .ifTrueBody contains form_eq evaluate fault⟩
  | .ifFalseBody contains form_eq evaluate fault =>
    obtain ⟨size_evaluate, evaluate⟩ := ExpressionEvaluates.has_size evaluate
    obtain ⟨size_fault, fault⟩ := StatementsFault.has_size fault
    exact ⟨_, .ifFalseBody contains form_eq evaluate fault⟩
  | .block contains form_eq fault =>
    obtain ⟨size_fault, fault⟩ := StatementsFault.has_size fault
    exact ⟨_, .block contains form_eq fault⟩
  | .matchScrutinee contains form_eq fault =>
    obtain ⟨size_fault, fault⟩ := ExpressionFaults.has_size fault
    exact ⟨_, .matchScrutinee contains form_eq fault⟩
  | .matchPattern contains form_eq scrutinee_contains scrutinee_evaluates allocate_hidden fault =>
    obtain ⟨size_scrutinee_evaluates, scrutinee_evaluates⟩ := ExpressionEvaluates.has_size scrutinee_evaluates
    exact ⟨_, .matchPattern contains form_eq scrutinee_contains scrutinee_evaluates allocate_hidden fault⟩
  | .matchArmBody contains form_eq scrutinee_contains scrutinee_evaluates allocate_hidden select binders_eq values_eq binders_extend allocate_bindings fault =>
    obtain ⟨size_scrutinee_evaluates, scrutinee_evaluates⟩ := ExpressionEvaluates.has_size scrutinee_evaluates
    obtain ⟨size_fault, fault⟩ := StatementsFault.has_size fault
    exact ⟨_, .matchArmBody contains form_eq scrutinee_contains scrutinee_evaluates allocate_hidden select binders_eq values_eq binders_extend allocate_bindings fault⟩
  | .matchDefaultBody contains form_eq scrutinee_contains scrutinee_evaluates allocate_hidden select fault =>
    obtain ⟨size_scrutinee_evaluates, scrutinee_evaluates⟩ := ExpressionEvaluates.has_size scrutinee_evaluates
    obtain ⟨size_fault, fault⟩ := StatementsFault.has_size fault
    exact ⟨_, .matchDefaultBody contains form_eq scrutinee_contains scrutinee_evaluates allocate_hidden select fault⟩
  | .forInitializer contains form_eq fault =>
    obtain ⟨size_fault, fault⟩ := ForItemsFault.has_size fault
    exact ⟨_, .forInitializer contains form_eq fault⟩
  | .forIteration contains form_eq initializer_executes fault =>
    obtain ⟨size_initializer_executes, initializer_executes⟩ := ForItemsExecute.has_size initializer_executes
    obtain ⟨size_fault, fault⟩ := ForLoopFaults.has_size fault
    exact ⟨_, .forIteration contains form_eq initializer_executes fault⟩
  | .whileIteration contains form_eq fault =>
    obtain ⟨size_fault, fault⟩ := WhileFaults.has_size fault
    exact ⟨_, .whileIteration contains form_eq fault⟩
termination_by structural trace

theorem StatementsFault.has_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : List StatementId} {a6 : Context} {a7 : SemanticFault} {a8 : Heap}
    (trace : Dynamic.StatementsFault program a0 a1 a2 a3 a4 a5 a6 a7 a8) : ∃ size, StatementsFault program size a0 a1 a2 a3 a4 a5 a6 a7 a8 := by
  match trace with
  | .head fault =>
    obtain ⟨size_fault, fault⟩ := StatementFaults.has_size fault
    exact ⟨_, .head fault⟩
  | .tail head fault =>
    obtain ⟨size_head, head⟩ := StatementExecutes.has_size head
    obtain ⟨size_fault, fault⟩ := StatementsFault.has_size fault
    exact ⟨_, .tail head fault⟩
termination_by structural trace

theorem FunctionStatementsFault.has_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : List StatementId} {a6 : Context} {a7 : SemanticFault} {a8 : Heap}
    (trace : Dynamic.FunctionStatementsFault program a0 a1 a2 a3 a4 a5 a6 a7 a8) : ∃ size, FunctionStatementsFault program size a0 a1 a2 a3 a4 a5 a6 a7 a8 := by
  match trace with
  | .singleton fault =>
    obtain ⟨size_fault, fault⟩ := StatementFaults.has_size fault
    exact ⟨_, .singleton fault⟩
  | .tailExpression contains form_eq fault =>
    obtain ⟨size_fault, fault⟩ := ExpressionFaults.has_size fault
    exact ⟨_, .tailExpression contains form_eq fault⟩
  | .head fault =>
    obtain ⟨size_fault, fault⟩ := StatementFaults.has_size fault
    exact ⟨_, .head fault⟩
  | .tail head fault =>
    obtain ⟨size_head, head⟩ := StatementExecutes.has_size head
    obtain ⟨size_fault, fault⟩ := FunctionStatementsFault.has_size fault
    exact ⟨_, .tail head fault⟩
termination_by structural trace

theorem SourcePlaceFaults.has_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : PlaceResolution} {a6 : SemanticFault} {a7 : Heap}
    (trace : Dynamic.SourcePlaceFaults program a0 a1 a2 a3 a4 a5 a6 a7) : ∃ size, SourcePlaceFaults program size a0 a1 a2 a3 a4 a5 a6 a7 := by
  match trace with
  | .unbound missing =>
    exact ⟨_, .unbound missing⟩
  | .dangling lookup missing =>
    exact ⟨_, .dangling lookup missing⟩
  | .projectionExpression lookup read fault =>
    obtain ⟨size_fault, fault⟩ := SourceProjectionsFault.has_size fault
    exact ⟨_, .projectionExpression lookup read fault⟩
  | .danglingAfterProjections lookup read evaluate missing =>
    obtain ⟨size_evaluate, evaluate⟩ := SourceProjectionsEvaluate.has_size evaluate
    exact ⟨_, .danglingAfterProjections lookup read evaluate missing⟩
  | .projectionRead lookup initial_read evaluate current_read initial_value fault =>
    obtain ⟨size_evaluate, evaluate⟩ := SourceProjectionsEvaluate.has_size evaluate
    exact ⟨_, .projectionRead lookup initial_read evaluate current_read initial_value fault⟩
  | .uninitialized lookup initial_read evaluate current_read empty not_mapping has_projection =>
    obtain ⟨size_evaluate, evaluate⟩ := SourceProjectionsEvaluate.has_size evaluate
    exact ⟨_, .uninitialized lookup initial_read evaluate current_read empty not_mapping has_projection⟩
termination_by structural trace

theorem SourceProjectionsFault.has_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : List PlaceProjection} {a6 : SemanticFault} {a7 : Heap}
    (trace : Dynamic.SourceProjectionsFault program a0 a1 a2 a3 a4 a5 a6 a7) : ∃ size, SourceProjectionsFault program size a0 a1 a2 a3 a4 a5 a6 a7 := by
  match trace with
  | .indexHead fault =>
    obtain ⟨size_fault, fault⟩ := ExpressionFaults.has_size fault
    exact ⟨_, .indexHead fault⟩
  | .indexTail head fault =>
    obtain ⟨size_head, head⟩ := ExpressionEvaluates.has_size head
    obtain ⟨size_fault, fault⟩ := SourceProjectionsFault.has_size fault
    exact ⟨_, .indexTail head fault⟩
  | .memberTail fault =>
    obtain ⟨size_fault, fault⟩ := SourceProjectionsFault.has_size fault
    exact ⟨_, .memberTail fault⟩
termination_by structural trace

theorem SourcePlaceAssignmentFaults.has_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : PlaceResolution} {a6 : Syntax.ValueAssignOp} {a7 : ExpressionId} {a8 : SemanticFault} {a9 : Heap}
    (trace : Dynamic.SourcePlaceAssignmentFaults program a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) : ∃ size, SourcePlaceAssignmentFaults program size a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 := by
  match trace with
  | .target fault =>
    obtain ⟨size_fault, fault⟩ := SourcePlaceFaults.has_size fault
    exact ⟨_, .target fault⟩
  | .rhs resolve fault =>
    obtain ⟨size_resolve, resolve⟩ := SourcePlaceResolves.has_size resolve
    obtain ⟨size_fault, fault⟩ := ExpressionFaults.has_size fault
    exact ⟨_, .rhs resolve fault⟩
  | .operands resolve evaluate current_read root_type_eq initial_value path_read invalid =>
    obtain ⟨size_resolve, resolve⟩ := SourcePlaceResolves.has_size resolve
    obtain ⟨size_evaluate, evaluate⟩ := ExpressionEvaluates.has_size evaluate
    exact ⟨_, .operands resolve evaluate current_read root_type_eq initial_value path_read invalid⟩
  | .structuralUpdate resolve evaluate current_read root_type_eq initial_value fault =>
    obtain ⟨size_resolve, resolve⟩ := SourcePlaceResolves.has_size resolve
    obtain ⟨size_evaluate, evaluate⟩ := ExpressionEvaluates.has_size evaluate
    exact ⟨_, .structuralUpdate resolve evaluate current_read root_type_eq initial_value fault⟩
termination_by structural trace

theorem SourcePlaceBitNotFaults.has_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : PlaceResolution} {a6 : SemanticFault} {a7 : Heap}
    (trace : Dynamic.SourcePlaceBitNotFaults program a0 a1 a2 a3 a4 a5 a6 a7) : ∃ size, SourcePlaceBitNotFaults program size a0 a1 a2 a3 a4 a5 a6 a7 := by
  match trace with
  | .target fault =>
    obtain ⟨size_fault, fault⟩ := SourcePlaceFaults.has_size fault
    exact ⟨_, .target fault⟩
  | .uninitialized resolve empty =>
    obtain ⟨size_resolve, resolve⟩ := SourcePlaceResolves.has_size resolve
    exact ⟨_, .uninitialized resolve empty⟩
  | .operand resolve selected invalid =>
    obtain ⟨size_resolve, resolve⟩ := SourcePlaceResolves.has_size resolve
    exact ⟨_, .operand resolve selected invalid⟩
termination_by structural trace

theorem ForItemFaults.has_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : ForItemForm} {a6 : SemanticFault} {a7 : Heap}
    (trace : Dynamic.ForItemFaults program a0 a1 a2 a3 a4 a5 a6 a7) : ∃ size, ForItemFaults program size a0 a1 a2 a3 a4 a5 a6 a7 := by
  match trace with
  | .polymorphicLet polymorphic unsupported =>
    exact ⟨_, .polymorphicLet polymorphic unsupported⟩
  | .letInitializer monomorphic fault =>
    obtain ⟨size_fault, fault⟩ := ExpressionFaults.has_size fault
    exact ⟨_, .letInitializer monomorphic fault⟩
  | .expression fault =>
    obtain ⟨size_fault, fault⟩ := ExpressionFaults.has_size fault
    exact ⟨_, .expression fault⟩
  | .assignValue fault =>
    obtain ⟨size_fault, fault⟩ := SourcePlaceAssignmentFaults.has_size fault
    exact ⟨_, .assignValue fault⟩
  | .assignBitNot fault =>
    obtain ⟨size_fault, fault⟩ := SourcePlaceBitNotFaults.has_size fault
    exact ⟨_, .assignBitNot fault⟩
termination_by structural trace

theorem ForItemsFault.has_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : List ForItemForm} {a6 : Context} {a7 : SemanticFault} {a8 : Heap}
    (trace : Dynamic.ForItemsFault program a0 a1 a2 a3 a4 a5 a6 a7 a8) : ∃ size, ForItemsFault program size a0 a1 a2 a3 a4 a5 a6 a7 a8 := by
  match trace with
  | .head fault =>
    obtain ⟨size_fault, fault⟩ := ForItemFaults.has_size fault
    exact ⟨_, .head fault⟩
  | .tail head fault =>
    obtain ⟨size_head, head⟩ := ForItemExecutes.has_size head
    obtain ⟨size_fault, fault⟩ := ForItemsFault.has_size fault
    exact ⟨_, .tail head fault⟩
termination_by structural trace

theorem WhileFaults.has_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : ExpressionId} {a6 : List StatementId} {a7 : SemanticFault} {a8 : Heap}
    (trace : Dynamic.WhileFaults program a0 a1 a2 a3 a4 a5 a6 a7 a8) : ∃ size, WhileFaults program size a0 a1 a2 a3 a4 a5 a6 a7 a8 := by
  match trace with
  | .condition fault =>
    obtain ⟨size_fault, fault⟩ := ExpressionFaults.has_size fault
    exact ⟨_, .condition fault⟩
  | .conditionType evaluate not_boolean actual_type =>
    obtain ⟨size_evaluate, evaluate⟩ := ExpressionEvaluates.has_size evaluate
    exact ⟨_, .conditionType evaluate not_boolean actual_type⟩
  | .body condition_evaluates fault =>
    obtain ⟨size_condition_evaluates, condition_evaluates⟩ := ExpressionEvaluates.has_size condition_evaluates
    obtain ⟨size_fault, fault⟩ := StatementsFault.has_size fault
    exact ⟨_, .body condition_evaluates fault⟩
  | .nextFallthrough condition_evaluates body_executes fault =>
    obtain ⟨size_condition_evaluates, condition_evaluates⟩ := ExpressionEvaluates.has_size condition_evaluates
    obtain ⟨size_body_executes, body_executes⟩ := StatementsExecute.has_size body_executes
    obtain ⟨size_fault, fault⟩ := WhileFaults.has_size fault
    exact ⟨_, .nextFallthrough condition_evaluates body_executes fault⟩
  | .nextContinue condition_evaluates body_executes fault =>
    obtain ⟨size_condition_evaluates, condition_evaluates⟩ := ExpressionEvaluates.has_size condition_evaluates
    obtain ⟨size_body_executes, body_executes⟩ := StatementsExecute.has_size body_executes
    obtain ⟨size_fault, fault⟩ := WhileFaults.has_size fault
    exact ⟨_, .nextContinue condition_evaluates body_executes fault⟩
termination_by structural trace

theorem ForLoopFaults.has_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : ExpressionId} {a6 : List ForItemForm} {a7 : List StatementId} {a8 : SemanticFault} {a9 : Heap}
    (trace : Dynamic.ForLoopFaults program a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) : ∃ size, ForLoopFaults program size a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 := by
  match trace with
  | .condition fault =>
    obtain ⟨size_fault, fault⟩ := ExpressionFaults.has_size fault
    exact ⟨_, .condition fault⟩
  | .conditionType evaluate not_boolean actual_type =>
    obtain ⟨size_evaluate, evaluate⟩ := ExpressionEvaluates.has_size evaluate
    exact ⟨_, .conditionType evaluate not_boolean actual_type⟩
  | .body condition_evaluates fault =>
    obtain ⟨size_condition_evaluates, condition_evaluates⟩ := ExpressionEvaluates.has_size condition_evaluates
    obtain ⟨size_fault, fault⟩ := StatementsFault.has_size fault
    exact ⟨_, .body condition_evaluates fault⟩
  | .postFallthrough condition_evaluates body_executes fault =>
    obtain ⟨size_condition_evaluates, condition_evaluates⟩ := ExpressionEvaluates.has_size condition_evaluates
    obtain ⟨size_body_executes, body_executes⟩ := StatementsExecute.has_size body_executes
    obtain ⟨size_fault, fault⟩ := ForItemsFault.has_size fault
    exact ⟨_, .postFallthrough condition_evaluates body_executes fault⟩
  | .postContinue condition_evaluates body_executes fault =>
    obtain ⟨size_condition_evaluates, condition_evaluates⟩ := ExpressionEvaluates.has_size condition_evaluates
    obtain ⟨size_body_executes, body_executes⟩ := StatementsExecute.has_size body_executes
    obtain ⟨size_fault, fault⟩ := ForItemsFault.has_size fault
    exact ⟨_, .postContinue condition_evaluates body_executes fault⟩
  | .nextFallthrough condition_evaluates body_executes post_executes fault =>
    obtain ⟨size_condition_evaluates, condition_evaluates⟩ := ExpressionEvaluates.has_size condition_evaluates
    obtain ⟨size_body_executes, body_executes⟩ := StatementsExecute.has_size body_executes
    obtain ⟨size_post_executes, post_executes⟩ := ForItemsExecute.has_size post_executes
    obtain ⟨size_fault, fault⟩ := ForLoopFaults.has_size fault
    exact ⟨_, .nextFallthrough condition_evaluates body_executes post_executes fault⟩
  | .nextContinue condition_evaluates body_executes post_executes fault =>
    obtain ⟨size_condition_evaluates, condition_evaluates⟩ := ExpressionEvaluates.has_size condition_evaluates
    obtain ⟨size_body_executes, body_executes⟩ := StatementsExecute.has_size body_executes
    obtain ⟨size_post_executes, post_executes⟩ := ForItemsExecute.has_size post_executes
    obtain ⟨size_fault, fault⟩ := ForLoopFaults.has_size fault
    exact ⟨_, .nextContinue condition_evaluates body_executes post_executes fault⟩
termination_by structural trace

end

theorem ExpressionFaults.positive {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : ExpressionId} {a6 : SemanticFault} {a7 : Heap}
    (trace : ExpressionFaults program size a0 a1 a2 a3 a4 a5 a6 a7) : 0 < size := by
  cases trace <;> exact stepSize_positive _

theorem ExpressionFaults.iff_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : ExpressionId} {a6 : SemanticFault} {a7 : Heap} :
    Dynamic.ExpressionFaults program a0 a1 a2 a3 a4 a5 a6 a7 ↔ ∃ size, ExpressionFaults program size a0 a1 a2 a3 a4 a5 a6 a7 :=
  ⟨ExpressionFaults.has_size, fun ⟨_, sized⟩ => sized.sound⟩

theorem ExpressionFaults.children_below {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : ExpressionId} {a6 : SemanticFault} {a7 : Heap}
    (trace : ExpressionFaults program size a0 a1 a2 a3 a4 a5 a6 a7) :
    ∃ children : List Nat, size = stepSize children ∧ ∀ child ∈ children, child < size := by
  cases trace with
  | @missing _ _ _ _ _ _ _ =>
    exact ⟨[], rfl, fun _ member => child_lt_stepSize member⟩
  | @form size_fault _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_fault], rfl, fun _ member => child_lt_stepSize member⟩
  | @coercion size_form size_fault _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_form, size_fault], rfl, fun _ member => child_lt_stepSize member⟩
  | @generalizedLocalRequirement _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[], rfl, fun _ member => child_lt_stepSize member⟩
  | @generalizedLocalCoercion size_fault _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_fault], rfl, fun _ member => child_lt_stepSize member⟩

theorem ExpressionFormFaults.positive {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : ExpressionForm} {a6 : List RequirementId} {a7 : List CoercionStep} {a8 : SemanticFault} {a9 : Heap}
    (trace : ExpressionFormFaults program size a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) : 0 < size := by
  cases trace <;> exact stepSize_positive _

theorem ExpressionFormFaults.iff_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : ExpressionForm} {a6 : List RequirementId} {a7 : List CoercionStep} {a8 : SemanticFault} {a9 : Heap} :
    Dynamic.ExpressionFormFaults program a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 ↔ ∃ size, ExpressionFormFaults program size a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 :=
  ⟨ExpressionFormFaults.has_size, fun ⟨_, sized⟩ => sized.sound⟩

theorem ExpressionFormFaults.children_below {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : ExpressionForm} {a6 : List RequirementId} {a7 : List CoercionStep} {a8 : SemanticFault} {a9 : Heap}
    (trace : ExpressionFormFaults program size a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) :
    ∃ children : List Nat, size = stepSize children ∧ ∀ child ∈ children, child < size := by
  cases trace with
  | @integerRequirement _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[], rfl, fun _ member => child_lt_stepSize member⟩
  | @localUnbound _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[], rfl, fun _ member => child_lt_stepSize member⟩
  | @localDangling _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[], rfl, fun _ member => child_lt_stepSize member⟩
  | @localUninitialized _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[], rfl, fun _ member => child_lt_stepSize member⟩
  | @declarationRequirement _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[], rfl, fun _ member => child_lt_stepSize member⟩
  | @group size_fault _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_fault], rfl, fun _ member => child_lt_stepSize member⟩
  | @tuple size_fault _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_fault], rfl, fun _ member => child_lt_stepSize member⟩
  | @unaryOperand size_fault _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_fault], rfl, fun _ member => child_lt_stepSize member⟩
  | @unaryApply size_operand_evaluates size_fault _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_operand_evaluates, size_fault], rfl, fun _ member => child_lt_stepSize member⟩
  | @binaryLeft size_fault _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_fault], rfl, fun _ member => child_lt_stepSize member⟩
  | @binaryLeftOperand size_left_evaluates _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_left_evaluates], rfl, fun _ member => child_lt_stepSize member⟩
  | @binaryRight size_left_evaluates size_fault _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_left_evaluates, size_fault], rfl, fun _ member => child_lt_stepSize member⟩
  | @binaryApply size_left_evaluates size_right_evaluates size_fault _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_left_evaluates, size_right_evaluates, size_fault], rfl, fun _ member => child_lt_stepSize member⟩
  | @conditionalCondition size_fault _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_fault], rfl, fun _ member => child_lt_stepSize member⟩
  | @conditionalType size_condition_evaluates _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_condition_evaluates], rfl, fun _ member => child_lt_stepSize member⟩
  | @conditionalTrueBranch size_condition_evaluates size_fault _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_condition_evaluates, size_fault], rfl, fun _ member => child_lt_stepSize member⟩
  | @conditionalFalseBranch size_condition_evaluates size_fault _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_condition_evaluates, size_fault], rfl, fun _ member => child_lt_stepSize member⟩
  | @directCalleeMissing _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[], rfl, fun _ member => child_lt_stepSize member⟩
  | @directArguments size_fault _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_fault], rfl, fun _ member => child_lt_stepSize member⟩
  | @directRequirements size_arguments_evaluate _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_arguments_evaluate], rfl, fun _ member => child_lt_stepSize member⟩
  | @directApply size_arguments_evaluate size_fault _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_arguments_evaluate, size_fault], rfl, fun _ member => child_lt_stepSize member⟩
  | @builtinArguments size_fault _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_fault], rfl, fun _ member => child_lt_stepSize member⟩
  | @builtinApply size_arguments_evaluate size_fault _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_arguments_evaluate, size_fault], rfl, fun _ member => child_lt_stepSize member⟩
  | @indirectCallee size_fault _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_fault], rfl, fun _ member => child_lt_stepSize member⟩
  | @indirectNotCallable size_callee_evaluates _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_callee_evaluates], rfl, fun _ member => child_lt_stepSize member⟩
  | @indirectArguments size_callee_evaluates size_fault _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_callee_evaluates, size_fault], rfl, fun _ member => child_lt_stepSize member⟩
  | @indirectSourceArity size_callee_evaluates size_arguments_evaluate _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_callee_evaluates, size_arguments_evaluate], rfl, fun _ member => child_lt_stepSize member⟩
  | @indirectArgumentCoercion size_callee_evaluates size_arguments_evaluate size_fault _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_callee_evaluates, size_arguments_evaluate, size_fault], rfl, fun _ member => child_lt_stepSize member⟩
  | @indirectApply size_callee_evaluates size_arguments_evaluate size_argument_coercions size_fault _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_callee_evaluates, size_arguments_evaluate, size_argument_coercions, size_fault], rfl, fun _ member => child_lt_stepSize member⟩
  | @constructorArgument size_fault _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_fault], rfl, fun _ member => child_lt_stepSize member⟩
  | @constructorMetadata _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[], rfl, fun _ member => child_lt_stepSize member⟩
  | @memberBase size_fault _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_fault], rfl, fun _ member => child_lt_stepSize member⟩
  | @memberShape size_base_evaluates _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_base_evaluates], rfl, fun _ member => child_lt_stepSize member⟩
  | @memberIndex size_base_evaluates _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_base_evaluates], rfl, fun _ member => child_lt_stepSize member⟩
  | @indexBase size_fault _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_fault], rfl, fun _ member => child_lt_stepSize member⟩
  | @indexKey size_base_evaluates size_fault _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_base_evaluates, size_fault], rfl, fun _ member => child_lt_stepSize member⟩
  | @indexShape size_base_evaluates size_index_evaluates _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_base_evaluates, size_index_evaluates], rfl, fun _ member => child_lt_stepSize member⟩
  | @indexKeyType size_base_evaluates size_index_evaluates _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_base_evaluates, size_index_evaluates], rfl, fun _ member => child_lt_stepSize member⟩
  | @indexDefaultUnavailable size_base_evaluates size_index_evaluates _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_base_evaluates, size_index_evaluates], rfl, fun _ member => child_lt_stepSize member⟩

theorem ExpressionsFault.positive {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : List ExpressionId} {a6 : SemanticFault} {a7 : Heap}
    (trace : ExpressionsFault program size a0 a1 a2 a3 a4 a5 a6 a7) : 0 < size := by
  cases trace <;> exact stepSize_positive _

theorem ExpressionsFault.iff_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : List ExpressionId} {a6 : SemanticFault} {a7 : Heap} :
    Dynamic.ExpressionsFault program a0 a1 a2 a3 a4 a5 a6 a7 ↔ ∃ size, ExpressionsFault program size a0 a1 a2 a3 a4 a5 a6 a7 :=
  ⟨ExpressionsFault.has_size, fun ⟨_, sized⟩ => sized.sound⟩

theorem ExpressionsFault.children_below {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : List ExpressionId} {a6 : SemanticFault} {a7 : Heap}
    (trace : ExpressionsFault program size a0 a1 a2 a3 a4 a5 a6 a7) :
    ∃ children : List Nat, size = stepSize children ∧ ∀ child ∈ children, child < size := by
  cases trace with
  | @head size_fault _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_fault], rfl, fun _ member => child_lt_stepSize member⟩
  | @tail size_head size_fault _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_head, size_fault], rfl, fun _ member => child_lt_stepSize member⟩

theorem UnaryOperationFaults.positive {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : Heap} {a3 : Syntax.UnaryOp} {a4 : List RequirementId} {a5 : Value} {a6 : SemanticFault} {a7 : Heap}
    (trace : UnaryOperationFaults program size a0 a1 a2 a3 a4 a5 a6 a7) : 0 < size := by
  cases trace <;> exact stepSize_positive _

theorem UnaryOperationFaults.iff_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : Heap} {a3 : Syntax.UnaryOp} {a4 : List RequirementId} {a5 : Value} {a6 : SemanticFault} {a7 : Heap} :
    Dynamic.UnaryOperationFaults program a0 a1 a2 a3 a4 a5 a6 a7 ↔ ∃ size, UnaryOperationFaults program size a0 a1 a2 a3 a4 a5 a6 a7 :=
  ⟨UnaryOperationFaults.has_size, fun ⟨_, sized⟩ => sized.sound⟩

theorem UnaryOperationFaults.children_below {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : Heap} {a3 : Syntax.UnaryOp} {a4 : List RequirementId} {a5 : Value} {a6 : SemanticFault} {a7 : Heap}
    (trace : UnaryOperationFaults program size a0 a1 a2 a3 a4 a5 a6 a7) :
    ∃ children : List Nat, size = stepSize children ∧ ∀ child ∈ children, child < size := by
  cases trace with
  | @primitive _ _ _ _ _ _ =>
    exact ⟨[], rfl, fun _ member => child_lt_stepSize member⟩
  | @requirement _ _ _ _ _ _ _ _ =>
    exact ⟨[], rfl, fun _ member => child_lt_stepSize member⟩
  | @method size_fault _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_fault], rfl, fun _ member => child_lt_stepSize member⟩

theorem BinaryOperationFaults.positive {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : Heap} {a3 : Syntax.BinaryOp} {a4 : List RequirementId} {a5 : Value} {a6 : Value} {a7 : SemanticFault} {a8 : Heap}
    (trace : BinaryOperationFaults program size a0 a1 a2 a3 a4 a5 a6 a7 a8) : 0 < size := by
  cases trace <;> exact stepSize_positive _

theorem BinaryOperationFaults.iff_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : Heap} {a3 : Syntax.BinaryOp} {a4 : List RequirementId} {a5 : Value} {a6 : Value} {a7 : SemanticFault} {a8 : Heap} :
    Dynamic.BinaryOperationFaults program a0 a1 a2 a3 a4 a5 a6 a7 a8 ↔ ∃ size, BinaryOperationFaults program size a0 a1 a2 a3 a4 a5 a6 a7 a8 :=
  ⟨BinaryOperationFaults.has_size, fun ⟨_, sized⟩ => sized.sound⟩

theorem BinaryOperationFaults.children_below {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : Heap} {a3 : Syntax.BinaryOp} {a4 : List RequirementId} {a5 : Value} {a6 : Value} {a7 : SemanticFault} {a8 : Heap}
    (trace : BinaryOperationFaults program size a0 a1 a2 a3 a4 a5 a6 a7 a8) :
    ∃ children : List Nat, size = stepSize children ∧ ∀ child ∈ children, child < size := by
  cases trace with
  | @primitive _ _ _ _ _ _ _ =>
    exact ⟨[], rfl, fun _ member => child_lt_stepSize member⟩
  | @requirement _ _ _ _ _ _ _ _ _ =>
    exact ⟨[], rfl, fun _ member => child_lt_stepSize member⟩
  | @method size_fault _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_fault], rfl, fun _ member => child_lt_stepSize member⟩

theorem CoercionStepFaults.positive {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : Heap} {a3 : CoercionStep} {a4 : Value} {a5 : SemanticFault} {a6 : Heap}
    (trace : CoercionStepFaults program size a0 a1 a2 a3 a4 a5 a6) : 0 < size := by
  cases trace <;> exact stepSize_positive _

theorem CoercionStepFaults.iff_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : Heap} {a3 : CoercionStep} {a4 : Value} {a5 : SemanticFault} {a6 : Heap} :
    Dynamic.CoercionStepFaults program a0 a1 a2 a3 a4 a5 a6 ↔ ∃ size, CoercionStepFaults program size a0 a1 a2 a3 a4 a5 a6 :=
  ⟨CoercionStepFaults.has_size, fun ⟨_, sized⟩ => sized.sound⟩

theorem CoercionStepFaults.children_below {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : Heap} {a3 : CoercionStep} {a4 : Value} {a5 : SemanticFault} {a6 : Heap}
    (trace : CoercionStepFaults program size a0 a1 a2 a3 a4 a5 a6) :
    ∃ children : List Nat, size = stepSize children ∧ ∀ child ∈ children, child < size := by
  cases trace with
  | @requirement _ _ _ _ _ _ _ =>
    exact ⟨[], rfl, fun _ member => child_lt_stepSize member⟩
  | @primitiveInput _ _ _ _ _ _ _ _ _ =>
    exact ⟨[], rfl, fun _ member => child_lt_stepSize member⟩
  | @method size_fault _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_fault], rfl, fun _ member => child_lt_stepSize member⟩

theorem CoercionPathFaults.positive {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : Heap} {a3 : List CoercionStep} {a4 : Value} {a5 : SemanticFault} {a6 : Heap}
    (trace : CoercionPathFaults program size a0 a1 a2 a3 a4 a5 a6) : 0 < size := by
  cases trace <;> exact stepSize_positive _

theorem CoercionPathFaults.iff_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : Heap} {a3 : List CoercionStep} {a4 : Value} {a5 : SemanticFault} {a6 : Heap} :
    Dynamic.CoercionPathFaults program a0 a1 a2 a3 a4 a5 a6 ↔ ∃ size, CoercionPathFaults program size a0 a1 a2 a3 a4 a5 a6 :=
  ⟨CoercionPathFaults.has_size, fun ⟨_, sized⟩ => sized.sound⟩

theorem CoercionPathFaults.children_below {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : Heap} {a3 : List CoercionStep} {a4 : Value} {a5 : SemanticFault} {a6 : Heap}
    (trace : CoercionPathFaults program size a0 a1 a2 a3 a4 a5 a6) :
    ∃ children : List Nat, size = stepSize children ∧ ∀ child ∈ children, child < size := by
  cases trace with
  | @head size_fault _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_fault], rfl, fun _ member => child_lt_stepSize member⟩
  | @tail size_head size_fault _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_head, size_fault], rfl, fun _ member => child_lt_stepSize member⟩

theorem CallableFaults.positive {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : EvidenceEnvironment} {a3 : Heap} {a4 : Value} {a5 : List Value} {a6 : SemanticFault} {a7 : Heap}
    (trace : CallableFaults program size a0 a1 a2 a3 a4 a5 a6 a7) : 0 < size := by
  cases trace <;> exact stepSize_positive _

theorem CallableFaults.iff_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : EvidenceEnvironment} {a3 : Heap} {a4 : Value} {a5 : List Value} {a6 : SemanticFault} {a7 : Heap} :
    Dynamic.CallableFaults program a0 a1 a2 a3 a4 a5 a6 a7 ↔ ∃ size, CallableFaults program size a0 a1 a2 a3 a4 a5 a6 a7 :=
  ⟨CallableFaults.has_size, fun ⟨_, sized⟩ => sized.sound⟩

theorem CallableFaults.children_below {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : EvidenceEnvironment} {a3 : Heap} {a4 : Value} {a5 : List Value} {a6 : SemanticFault} {a7 : Heap}
    (trace : CallableFaults program size a0 a1 a2 a3 a4 a5 a6 a7) :
    ∃ children : List Nat, size = stepSize children ∧ ∀ child ∈ children, child < size := by
  cases trace with
  | @notCallable _ _ _ _ _ _ _ =>
    exact ⟨[], rfl, fun _ member => child_lt_stepSize member⟩
  | @builtinArity _ _ _ _ _ _ _ =>
    exact ⟨[], rfl, fun _ member => child_lt_stepSize member⟩
  | @builtinArgumentType _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[], rfl, fun _ member => child_lt_stepSize member⟩
  | @globalSignatureMissing _ _ _ _ _ _ _ =>
    exact ⟨[], rfl, fun _ member => child_lt_stepSize member⟩
  | @globalBodyMissing _ _ _ _ _ _ _ =>
    exact ⟨[], rfl, fun _ member => child_lt_stepSize member⟩
  | @globalArity _ _ _ _ _ _ _ _ _ =>
    exact ⟨[], rfl, fun _ member => child_lt_stepSize member⟩
  | @globalBody size_fault _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_fault], rfl, fun _ member => child_lt_stepSize member⟩
  | @closureArity _ _ _ _ _ _ _ =>
    exact ⟨[], rfl, fun _ member => child_lt_stepSize member⟩
  | @closureBody size_fault _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_fault], rfl, fun _ member => child_lt_stepSize member⟩
  | @closureControlEscape size_execute _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_execute], rfl, fun _ member => child_lt_stepSize member⟩

theorem BodyFaults.positive {program : Program} {size : Nat} {a0 : BodyInstance} {a1 : EvidenceEnvironment} {a2 : Heap} {a3 : List Value} {a4 : SemanticFault} {a5 : Heap}
    (trace : BodyFaults program size a0 a1 a2 a3 a4 a5) : 0 < size := by
  cases trace <;> exact stepSize_positive _

theorem BodyFaults.iff_size {program : Program} {a0 : BodyInstance} {a1 : EvidenceEnvironment} {a2 : Heap} {a3 : List Value} {a4 : SemanticFault} {a5 : Heap} :
    Dynamic.BodyFaults program a0 a1 a2 a3 a4 a5 ↔ ∃ size, BodyFaults program size a0 a1 a2 a3 a4 a5 :=
  ⟨BodyFaults.has_size, fun ⟨_, sized⟩ => sized.sound⟩

theorem BodyFaults.children_below {program : Program} {size : Nat} {a0 : BodyInstance} {a1 : EvidenceEnvironment} {a2 : Heap} {a3 : List Value} {a4 : SemanticFault} {a5 : Heap}
    (trace : BodyFaults program size a0 a1 a2 a3 a4 a5) :
    ∃ children : List Nat, size = stepSize children ∧ ∀ child ∈ children, child < size := by
  cases trace with
  | @arity _ _ _ _ _ =>
    exact ⟨[], rfl, fun _ member => child_lt_stepSize member⟩
  | @statements size_fault _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_fault], rfl, fun _ member => child_lt_stepSize member⟩
  | @controlEscape size_execute _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_execute], rfl, fun _ member => child_lt_stepSize member⟩

theorem StatementFaults.positive {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : StatementId} {a6 : SemanticFault} {a7 : Heap}
    (trace : StatementFaults program size a0 a1 a2 a3 a4 a5 a6 a7) : 0 < size := by
  cases trace <;> exact stepSize_positive _

theorem StatementFaults.iff_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : StatementId} {a6 : SemanticFault} {a7 : Heap} :
    Dynamic.StatementFaults program a0 a1 a2 a3 a4 a5 a6 a7 ↔ ∃ size, StatementFaults program size a0 a1 a2 a3 a4 a5 a6 a7 :=
  ⟨StatementFaults.has_size, fun ⟨_, sized⟩ => sized.sound⟩

theorem StatementFaults.children_below {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : StatementId} {a6 : SemanticFault} {a7 : Heap}
    (trace : StatementFaults program size a0 a1 a2 a3 a4 a5 a6 a7) :
    ∃ children : List Nat, size = stepSize children ∧ ∀ child ∈ children, child < size := by
  cases trace with
  | @missing _ _ _ _ _ _ _ =>
    exact ⟨[], rfl, fun _ member => child_lt_stepSize member⟩
  | @polymorphicLet _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[], rfl, fun _ member => child_lt_stepSize member⟩
  | @letInitializer size_fault _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_fault], rfl, fun _ member => child_lt_stepSize member⟩
  | @returnValue size_fault _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_fault], rfl, fun _ member => child_lt_stepSize member⟩
  | @expression size_fault _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_fault], rfl, fun _ member => child_lt_stepSize member⟩
  | @assignValue size_fault _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_fault], rfl, fun _ member => child_lt_stepSize member⟩
  | @assignBitNot size_fault _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_fault], rfl, fun _ member => child_lt_stepSize member⟩
  | @ifCondition size_fault _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_fault], rfl, fun _ member => child_lt_stepSize member⟩
  | @ifConditionType size_evaluate _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_evaluate], rfl, fun _ member => child_lt_stepSize member⟩
  | @ifTrueBody size_evaluate size_fault _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_evaluate, size_fault], rfl, fun _ member => child_lt_stepSize member⟩
  | @ifFalseBody size_evaluate size_fault _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_evaluate, size_fault], rfl, fun _ member => child_lt_stepSize member⟩
  | @block size_fault _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_fault], rfl, fun _ member => child_lt_stepSize member⟩
  | @matchScrutinee size_fault _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_fault], rfl, fun _ member => child_lt_stepSize member⟩
  | @matchPattern size_scrutinee_evaluates _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_scrutinee_evaluates], rfl, fun _ member => child_lt_stepSize member⟩
  | @matchArmBody size_scrutinee_evaluates size_fault _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_scrutinee_evaluates, size_fault], rfl, fun _ member => child_lt_stepSize member⟩
  | @matchDefaultBody size_scrutinee_evaluates size_fault _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_scrutinee_evaluates, size_fault], rfl, fun _ member => child_lt_stepSize member⟩
  | @forInitializer size_fault _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_fault], rfl, fun _ member => child_lt_stepSize member⟩
  | @forIteration size_initializer_executes size_fault _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_initializer_executes, size_fault], rfl, fun _ member => child_lt_stepSize member⟩
  | @whileIteration size_fault _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_fault], rfl, fun _ member => child_lt_stepSize member⟩

theorem StatementsFault.positive {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : List StatementId} {a6 : Context} {a7 : SemanticFault} {a8 : Heap}
    (trace : StatementsFault program size a0 a1 a2 a3 a4 a5 a6 a7 a8) : 0 < size := by
  cases trace <;> exact stepSize_positive _

theorem StatementsFault.iff_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : List StatementId} {a6 : Context} {a7 : SemanticFault} {a8 : Heap} :
    Dynamic.StatementsFault program a0 a1 a2 a3 a4 a5 a6 a7 a8 ↔ ∃ size, StatementsFault program size a0 a1 a2 a3 a4 a5 a6 a7 a8 :=
  ⟨StatementsFault.has_size, fun ⟨_, sized⟩ => sized.sound⟩

theorem StatementsFault.children_below {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : List StatementId} {a6 : Context} {a7 : SemanticFault} {a8 : Heap}
    (trace : StatementsFault program size a0 a1 a2 a3 a4 a5 a6 a7 a8) :
    ∃ children : List Nat, size = stepSize children ∧ ∀ child ∈ children, child < size := by
  cases trace with
  | @head size_fault _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_fault], rfl, fun _ member => child_lt_stepSize member⟩
  | @tail size_head size_fault _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_head, size_fault], rfl, fun _ member => child_lt_stepSize member⟩

theorem FunctionStatementsFault.positive {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : List StatementId} {a6 : Context} {a7 : SemanticFault} {a8 : Heap}
    (trace : FunctionStatementsFault program size a0 a1 a2 a3 a4 a5 a6 a7 a8) : 0 < size := by
  cases trace <;> exact stepSize_positive _

theorem FunctionStatementsFault.iff_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : List StatementId} {a6 : Context} {a7 : SemanticFault} {a8 : Heap} :
    Dynamic.FunctionStatementsFault program a0 a1 a2 a3 a4 a5 a6 a7 a8 ↔ ∃ size, FunctionStatementsFault program size a0 a1 a2 a3 a4 a5 a6 a7 a8 :=
  ⟨FunctionStatementsFault.has_size, fun ⟨_, sized⟩ => sized.sound⟩

theorem FunctionStatementsFault.children_below {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : List StatementId} {a6 : Context} {a7 : SemanticFault} {a8 : Heap}
    (trace : FunctionStatementsFault program size a0 a1 a2 a3 a4 a5 a6 a7 a8) :
    ∃ children : List Nat, size = stepSize children ∧ ∀ child ∈ children, child < size := by
  cases trace with
  | @singleton size_fault _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_fault], rfl, fun _ member => child_lt_stepSize member⟩
  | @tailExpression size_fault _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_fault], rfl, fun _ member => child_lt_stepSize member⟩
  | @head size_fault _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_fault], rfl, fun _ member => child_lt_stepSize member⟩
  | @tail size_head size_fault _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_head, size_fault], rfl, fun _ member => child_lt_stepSize member⟩

theorem SourcePlaceFaults.positive {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : PlaceResolution} {a6 : SemanticFault} {a7 : Heap}
    (trace : SourcePlaceFaults program size a0 a1 a2 a3 a4 a5 a6 a7) : 0 < size := by
  cases trace <;> exact stepSize_positive _

theorem SourcePlaceFaults.iff_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : PlaceResolution} {a6 : SemanticFault} {a7 : Heap} :
    Dynamic.SourcePlaceFaults program a0 a1 a2 a3 a4 a5 a6 a7 ↔ ∃ size, SourcePlaceFaults program size a0 a1 a2 a3 a4 a5 a6 a7 :=
  ⟨SourcePlaceFaults.has_size, fun ⟨_, sized⟩ => sized.sound⟩

theorem SourcePlaceFaults.children_below {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : PlaceResolution} {a6 : SemanticFault} {a7 : Heap}
    (trace : SourcePlaceFaults program size a0 a1 a2 a3 a4 a5 a6 a7) :
    ∃ children : List Nat, size = stepSize children ∧ ∀ child ∈ children, child < size := by
  cases trace with
  | @unbound _ _ _ _ _ _ _ =>
    exact ⟨[], rfl, fun _ member => child_lt_stepSize member⟩
  | @dangling _ _ _ _ _ _ _ _ _ =>
    exact ⟨[], rfl, fun _ member => child_lt_stepSize member⟩
  | @projectionExpression size_fault _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_fault], rfl, fun _ member => child_lt_stepSize member⟩
  | @danglingAfterProjections size_evaluate _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_evaluate], rfl, fun _ member => child_lt_stepSize member⟩
  | @projectionRead size_evaluate _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_evaluate], rfl, fun _ member => child_lt_stepSize member⟩
  | @uninitialized size_evaluate _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_evaluate], rfl, fun _ member => child_lt_stepSize member⟩

theorem SourceProjectionsFault.positive {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : List PlaceProjection} {a6 : SemanticFault} {a7 : Heap}
    (trace : SourceProjectionsFault program size a0 a1 a2 a3 a4 a5 a6 a7) : 0 < size := by
  cases trace <;> exact stepSize_positive _

theorem SourceProjectionsFault.iff_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : List PlaceProjection} {a6 : SemanticFault} {a7 : Heap} :
    Dynamic.SourceProjectionsFault program a0 a1 a2 a3 a4 a5 a6 a7 ↔ ∃ size, SourceProjectionsFault program size a0 a1 a2 a3 a4 a5 a6 a7 :=
  ⟨SourceProjectionsFault.has_size, fun ⟨_, sized⟩ => sized.sound⟩

theorem SourceProjectionsFault.children_below {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : List PlaceProjection} {a6 : SemanticFault} {a7 : Heap}
    (trace : SourceProjectionsFault program size a0 a1 a2 a3 a4 a5 a6 a7) :
    ∃ children : List Nat, size = stepSize children ∧ ∀ child ∈ children, child < size := by
  cases trace with
  | @indexHead size_fault _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_fault], rfl, fun _ member => child_lt_stepSize member⟩
  | @indexTail size_head size_fault _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_head, size_fault], rfl, fun _ member => child_lt_stepSize member⟩
  | @memberTail size_fault _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_fault], rfl, fun _ member => child_lt_stepSize member⟩

theorem SourcePlaceAssignmentFaults.positive {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : PlaceResolution} {a6 : Syntax.ValueAssignOp} {a7 : ExpressionId} {a8 : SemanticFault} {a9 : Heap}
    (trace : SourcePlaceAssignmentFaults program size a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) : 0 < size := by
  cases trace <;> exact stepSize_positive _

theorem SourcePlaceAssignmentFaults.iff_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : PlaceResolution} {a6 : Syntax.ValueAssignOp} {a7 : ExpressionId} {a8 : SemanticFault} {a9 : Heap} :
    Dynamic.SourcePlaceAssignmentFaults program a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 ↔ ∃ size, SourcePlaceAssignmentFaults program size a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 :=
  ⟨SourcePlaceAssignmentFaults.has_size, fun ⟨_, sized⟩ => sized.sound⟩

theorem SourcePlaceAssignmentFaults.children_below {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : PlaceResolution} {a6 : Syntax.ValueAssignOp} {a7 : ExpressionId} {a8 : SemanticFault} {a9 : Heap}
    (trace : SourcePlaceAssignmentFaults program size a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) :
    ∃ children : List Nat, size = stepSize children ∧ ∀ child ∈ children, child < size := by
  cases trace with
  | @target size_fault _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_fault], rfl, fun _ member => child_lt_stepSize member⟩
  | @rhs size_resolve size_fault _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_resolve, size_fault], rfl, fun _ member => child_lt_stepSize member⟩
  | @operands size_resolve size_evaluate _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_resolve, size_evaluate], rfl, fun _ member => child_lt_stepSize member⟩
  | @structuralUpdate size_resolve size_evaluate _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_resolve, size_evaluate], rfl, fun _ member => child_lt_stepSize member⟩

theorem SourcePlaceBitNotFaults.positive {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : PlaceResolution} {a6 : SemanticFault} {a7 : Heap}
    (trace : SourcePlaceBitNotFaults program size a0 a1 a2 a3 a4 a5 a6 a7) : 0 < size := by
  cases trace <;> exact stepSize_positive _

theorem SourcePlaceBitNotFaults.iff_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : PlaceResolution} {a6 : SemanticFault} {a7 : Heap} :
    Dynamic.SourcePlaceBitNotFaults program a0 a1 a2 a3 a4 a5 a6 a7 ↔ ∃ size, SourcePlaceBitNotFaults program size a0 a1 a2 a3 a4 a5 a6 a7 :=
  ⟨SourcePlaceBitNotFaults.has_size, fun ⟨_, sized⟩ => sized.sound⟩

theorem SourcePlaceBitNotFaults.children_below {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : PlaceResolution} {a6 : SemanticFault} {a7 : Heap}
    (trace : SourcePlaceBitNotFaults program size a0 a1 a2 a3 a4 a5 a6 a7) :
    ∃ children : List Nat, size = stepSize children ∧ ∀ child ∈ children, child < size := by
  cases trace with
  | @target size_fault _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_fault], rfl, fun _ member => child_lt_stepSize member⟩
  | @uninitialized size_resolve _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_resolve], rfl, fun _ member => child_lt_stepSize member⟩
  | @operand size_resolve _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_resolve], rfl, fun _ member => child_lt_stepSize member⟩

theorem ForItemFaults.positive {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : ForItemForm} {a6 : SemanticFault} {a7 : Heap}
    (trace : ForItemFaults program size a0 a1 a2 a3 a4 a5 a6 a7) : 0 < size := by
  cases trace <;> exact stepSize_positive _

theorem ForItemFaults.iff_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : ForItemForm} {a6 : SemanticFault} {a7 : Heap} :
    Dynamic.ForItemFaults program a0 a1 a2 a3 a4 a5 a6 a7 ↔ ∃ size, ForItemFaults program size a0 a1 a2 a3 a4 a5 a6 a7 :=
  ⟨ForItemFaults.has_size, fun ⟨_, sized⟩ => sized.sound⟩

theorem ForItemFaults.children_below {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : ForItemForm} {a6 : SemanticFault} {a7 : Heap}
    (trace : ForItemFaults program size a0 a1 a2 a3 a4 a5 a6 a7) :
    ∃ children : List Nat, size = stepSize children ∧ ∀ child ∈ children, child < size := by
  cases trace with
  | @polymorphicLet _ _ _ _ _ _ _ _ _ =>
    exact ⟨[], rfl, fun _ member => child_lt_stepSize member⟩
  | @letInitializer size_fault _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_fault], rfl, fun _ member => child_lt_stepSize member⟩
  | @expression size_fault _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_fault], rfl, fun _ member => child_lt_stepSize member⟩
  | @assignValue size_fault _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_fault], rfl, fun _ member => child_lt_stepSize member⟩
  | @assignBitNot size_fault _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_fault], rfl, fun _ member => child_lt_stepSize member⟩

theorem ForItemsFault.positive {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : List ForItemForm} {a6 : Context} {a7 : SemanticFault} {a8 : Heap}
    (trace : ForItemsFault program size a0 a1 a2 a3 a4 a5 a6 a7 a8) : 0 < size := by
  cases trace <;> exact stepSize_positive _

theorem ForItemsFault.iff_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : List ForItemForm} {a6 : Context} {a7 : SemanticFault} {a8 : Heap} :
    Dynamic.ForItemsFault program a0 a1 a2 a3 a4 a5 a6 a7 a8 ↔ ∃ size, ForItemsFault program size a0 a1 a2 a3 a4 a5 a6 a7 a8 :=
  ⟨ForItemsFault.has_size, fun ⟨_, sized⟩ => sized.sound⟩

theorem ForItemsFault.children_below {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : List ForItemForm} {a6 : Context} {a7 : SemanticFault} {a8 : Heap}
    (trace : ForItemsFault program size a0 a1 a2 a3 a4 a5 a6 a7 a8) :
    ∃ children : List Nat, size = stepSize children ∧ ∀ child ∈ children, child < size := by
  cases trace with
  | @head size_fault _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_fault], rfl, fun _ member => child_lt_stepSize member⟩
  | @tail size_head size_fault _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_head, size_fault], rfl, fun _ member => child_lt_stepSize member⟩

theorem WhileFaults.positive {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : ExpressionId} {a6 : List StatementId} {a7 : SemanticFault} {a8 : Heap}
    (trace : WhileFaults program size a0 a1 a2 a3 a4 a5 a6 a7 a8) : 0 < size := by
  cases trace <;> exact stepSize_positive _

theorem WhileFaults.iff_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : ExpressionId} {a6 : List StatementId} {a7 : SemanticFault} {a8 : Heap} :
    Dynamic.WhileFaults program a0 a1 a2 a3 a4 a5 a6 a7 a8 ↔ ∃ size, WhileFaults program size a0 a1 a2 a3 a4 a5 a6 a7 a8 :=
  ⟨WhileFaults.has_size, fun ⟨_, sized⟩ => sized.sound⟩

theorem WhileFaults.children_below {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : ExpressionId} {a6 : List StatementId} {a7 : SemanticFault} {a8 : Heap}
    (trace : WhileFaults program size a0 a1 a2 a3 a4 a5 a6 a7 a8) :
    ∃ children : List Nat, size = stepSize children ∧ ∀ child ∈ children, child < size := by
  cases trace with
  | @condition size_fault _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_fault], rfl, fun _ member => child_lt_stepSize member⟩
  | @conditionType size_evaluate _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_evaluate], rfl, fun _ member => child_lt_stepSize member⟩
  | @body size_condition_evaluates size_fault _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_condition_evaluates, size_fault], rfl, fun _ member => child_lt_stepSize member⟩
  | @nextFallthrough size_condition_evaluates size_body_executes size_fault _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_condition_evaluates, size_body_executes, size_fault], rfl, fun _ member => child_lt_stepSize member⟩
  | @nextContinue size_condition_evaluates size_body_executes size_fault _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_condition_evaluates, size_body_executes, size_fault], rfl, fun _ member => child_lt_stepSize member⟩

theorem ForLoopFaults.positive {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : ExpressionId} {a6 : List ForItemForm} {a7 : List StatementId} {a8 : SemanticFault} {a9 : Heap}
    (trace : ForLoopFaults program size a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) : 0 < size := by
  cases trace <;> exact stepSize_positive _

theorem ForLoopFaults.iff_size {program : Program} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : ExpressionId} {a6 : List ForItemForm} {a7 : List StatementId} {a8 : SemanticFault} {a9 : Heap} :
    Dynamic.ForLoopFaults program a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 ↔ ∃ size, ForLoopFaults program size a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 :=
  ⟨ForLoopFaults.has_size, fun ⟨_, sized⟩ => sized.sound⟩

theorem ForLoopFaults.children_below {program : Program} {size : Nat} {a0 : Context} {a1 : EvidenceEnvironment} {a2 : TypedSource} {a3 : Dynamic.Environment} {a4 : Heap} {a5 : ExpressionId} {a6 : List ForItemForm} {a7 : List StatementId} {a8 : SemanticFault} {a9 : Heap}
    (trace : ForLoopFaults program size a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) :
    ∃ children : List Nat, size = stepSize children ∧ ∀ child ∈ children, child < size := by
  cases trace with
  | @condition size_fault _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_fault], rfl, fun _ member => child_lt_stepSize member⟩
  | @conditionType size_evaluate _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_evaluate], rfl, fun _ member => child_lt_stepSize member⟩
  | @body size_condition_evaluates size_fault _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_condition_evaluates, size_fault], rfl, fun _ member => child_lt_stepSize member⟩
  | @postFallthrough size_condition_evaluates size_body_executes size_fault _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_condition_evaluates, size_body_executes, size_fault], rfl, fun _ member => child_lt_stepSize member⟩
  | @postContinue size_condition_evaluates size_body_executes size_fault _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_condition_evaluates, size_body_executes, size_fault], rfl, fun _ member => child_lt_stepSize member⟩
  | @nextFallthrough size_condition_evaluates size_body_executes size_post_executes size_fault _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_condition_evaluates, size_body_executes, size_post_executes, size_fault], rfl, fun _ member => child_lt_stepSize member⟩
  | @nextContinue size_condition_evaluates size_body_executes size_post_executes size_fault _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    exact ⟨[size_condition_evaluates, size_body_executes, size_post_executes, size_fault], rfl, fun _ member => child_lt_stepSize member⟩

/-! ## Rule coverage

The first mutual group has 92 rules; the fault group has 130.
Each dynamic premise is assigned one size binder and appears once in the
constructor result sum. The table records rule and premise counts, in source
order; `children_below` covers every constructor in each family.

| Judgment | Rules | Dynamic premises |
| --- | ---: | ---: |
| `ExpressionEvaluates` | 2 | 3 |
| `ExpressionFormEvaluates` | 23 | 26 |
| `ExpressionsEvaluate` | 2 | 2 |
| `SourceProjectionsEvaluate` | 3 | 3 |
| `SourcePlaceResolves` | 1 | 1 |
| `SourcePlaceAssignment` | 1 | 2 |
| `SourcePlaceSnapshotUpdate` | 1 | 1 |
| `UnaryOperationApplies` | 2 | 1 |
| `BinaryOperationApplies` | 2 | 1 |
| `CoercionStepExecutes` | 2 | 1 |
| `CoercionPathExecutes` | 2 | 2 |
| `CallableApplies` | 4 | 3 |
| `BodyInvokes` | 2 | 2 |
| `StatementExecutes` | 19 | 19 |
| `StatementsExecute` | 3 | 3 |
| `FunctionStatementsExecute` | 5 | 5 |
| `ForItemExecutes` | 6 | 4 |
| `ForItemsExecute` | 2 | 2 |
| `WhileExecutes` | 5 | 11 |
| `ForLoopExecutes` | 5 | 13 |
| `ExpressionFaults` | 5 | 4 |
| `ExpressionFormFaults` | 39 | 51 |
| `ExpressionsFault` | 2 | 3 |
| `UnaryOperationFaults` | 3 | 1 |
| `BinaryOperationFaults` | 3 | 1 |
| `CoercionStepFaults` | 3 | 1 |
| `CoercionPathFaults` | 2 | 3 |
| `CallableFaults` | 10 | 3 |
| `BodyFaults` | 3 | 2 |
| `StatementFaults` | 19 | 22 |
| `StatementsFault` | 2 | 3 |
| `FunctionStatementsFault` | 4 | 5 |
| `SourcePlaceFaults` | 6 | 4 |
| `SourceProjectionsFault` | 3 | 4 |
| `SourcePlaceAssignmentFaults` | 4 | 7 |
| `SourcePlaceBitNotFaults` | 3 | 3 |
| `ForItemFaults` | 5 | 4 |
| `ForItemsFault` | 2 | 3 |
| `WhileFaults` | 5 | 10 |
| `ForLoopFaults` | 7 | 18 |
-/

end Solcore.SourceSemantics.CoreLowering.SourceExecutionSize
