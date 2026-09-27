import Solcore.SourceSemantics.Program
import Solcore.SourceSemantics.Substitution
import Solcore.SourceSemantics.Dynamic.Default
import Solcore.SourceSemantics.Dynamic.Evidence
import Solcore.SourceSemantics.Dynamic.GeneralizedClosure
import Solcore.SourceSemantics.Dynamic.LocalSchemes
import Solcore.SourceSemantics.Dynamic.Pattern
import Solcore.SourceSemantics.Dynamic.Place
import Solcore.SourceSemantics.Dynamic.Primitive

/-!
Fuel-free, declarative big-step dynamics for resolved source programs.

The judgments in this module consume forgeable occurrence tables.  Every
expression and statement step therefore carries an explicit table-membership
premise.  Generic calls use structural rigid-parameter substitution; they do
not invoke source inference, specialization discovery, or the executable
runtime.  Recursive calls and loops are represented by finite derivation
trees, rather than by an evaluator counter.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.Dynamic

open Frontend
open Frontend.SourceInference
open TypeSystem

/-- A rigidly instantiated dynamic view of one generic declaration body.
Lexical generalized-initializer variables are closed at invocation, while the
body-wide residual occurrence scope remains open. -/
structure BodyInstance where
  context : Context
  source : TypedSource
  resultType : Ty
  deriving Repr

/-- Structural instantiation of a cataloged top-level function body. -/
inductive FunctionInstantiates (program : Program)
    (instantiation : DeclarationInstantiation) : BodyInstance → Prop where
  | intro
      {signature : ProgramFunctionSignature}
      {definition : FunctionDefinition}
      {bodyInstance : BodyInstance}
      (signature_mem : signature ∈ program.signatures.functions)
      (definition_mem : definition ∈ program.functions)
      (declaration_eq : instantiation.declaration = signature.id)
      (owner_eq : definition.body.owner = signature.id)
      (valid : SourceSemantics.DeclarationInstantiation.Valid
        (Context.ofSignatures program.signatures) instantiation)
      (source_eq : bodyInstance.source =
        StructuralSubstitution.applyTypedSource
          instantiation.parameterSubstitution definition.body.source)
      (result_eq : bodyInstance.resultType =
        instantiation.parameterSubstitution.apply definition.body.resultType)
      (context_eq : bodyInstance.context =
        declarationContext program.signatures definition.body.owner []
          instantiation.predicates
          (definition.body.solvedRequirements.map
            (StructuralSubstitution.applySolvedRequirement
              instantiation.parameterSubstitution))) :
      FunctionInstantiates program instantiation bodyInstance

/-- Exact implementation-method instantiation, including the owning trait. -/
inductive TraitMethodInstantiates (program : Program)
    (implementation : ProgramImplementationSignature)
    (method : ProgramImplMethodSignature)
    (trait : ProgramTraitSignature)
    (definition : MethodDefinition)
    (substitution : ParameterSubstitution) : BodyInstance → Prop where
  | intro
      {bodyInstance : BodyInstance}
      (implementation_mem :
        implementation ∈ program.signatures.implementations)
      (method_mem : method ∈ implementation.methods)
      (trait_mem : trait ∈ program.signatures.traits)
      (trait_owner : method.traitMethod.trait = trait.id)
      (definition_mem : definition ∈ program.methods)
      (definition_id : definition.id = method.id)
      (owner_eq : definition.body.owner = implementation.id)
      (substitution_exact :
        SourceSemantics.ParameterSubstitution.Exact substitution
          implementation.parameters)
      (substitution_range :
        SourceSemantics.ParameterSubstitution.RangeWellFormed
          (Context.ofSignatures program.signatures) substitution)
      (source_eq : bodyInstance.source =
        StructuralSubstitution.applyTypedSource substitution
          definition.body.source)
      (result_eq : bodyInstance.resultType =
        substitution.apply definition.body.resultType)
      (context_eq : bodyInstance.context =
        declarationContext program.signatures definition.body.owner []
          ((methodAssumptions trait implementation method).map
            (ProgramPredicate.applyParameters substitution))
          (definition.body.solvedRequirements.map
            (StructuralSubstitution.applySolvedRequirement
              substitution))) :
      TraitMethodInstantiates program implementation method trait definition
        substitution bodyInstance

/-- Canonical source-order instantiation of an implementation head.  Exactness
excludes missing and unrelated parameters, while the key projection fixes the
otherwise extensionally irrelevant association-list order.  Whole-program
well-formedness separately requires every implementation parameter to occur in
the head, excluding phantom choices. -/
def ImplementationHeadDetermines
    (implementation : ProgramImplementationSignature)
    (goal : ProgramPredicate) (substitution : ParameterSubstitution) : Prop :=
  substitution.map Prod.fst = implementation.parameters ∧
    SourceSemantics.ParameterSubstitution.Exact substitution
      implementation.parameters ∧
    ProgramPredicate.applyParameters substitution implementation.head = goal

/-- A retained primary requirement selects one exact source method body. -/
inductive OperatorMethodSelected (program : Program) (context : Context)
    (callerEvidence : EvidenceEnvironment)
    (traitName methodName : String) :
    List RequirementId → BodyInstance → EvidenceEnvironment → Prop where
  | intro
      {primary : RequirementId} {methodRequirements : List RequirementId}
      {goal : ProgramPredicate} {closedEvidence : TraitEvidence}
      {implementation : ProgramImplementationSignature}
      {method : ProgramImplMethodSignature}
      {trait : ProgramTraitSignature}
      {definition : MethodDefinition}
      {substitution : ParameterSubstitution}
      {bodyInstance : BodyInstance}
      {methodEvidence calleeEvidence : EvidenceEnvironment}
      (selects : RequirementSelectsMethod program context callerEvidence
        primary goal methodName definition closedEvidence)
      (closed_shape : ∃ premises,
        closedEvidence = .implementation goal
          (.declaration implementation.id) premises)
      (implementation_mem :
        implementation ∈ program.signatures.implementations)
      (trait_mem : trait ∈ program.signatures.traits)
      (trait_name : trait.name = traitName)
      (goal_trait : goal.trait = .declaration trait.id)
      (head_determined : ImplementationHeadDetermines implementation goal
        substitution)
      (method_mem : method ∈ implementation.methods)
      (method_name : method.name = methodName)
      (method_owner : method.traitMethod.trait = trait.id)
      (method_requirements : RequirementsProduceEnvironment context
        callerEvidence
        methodRequirements
        (method.wherePredicates.map
          (ProgramPredicate.applyParameters substitution)) methodEvidence)
      (instantiates : TraitMethodInstantiates program implementation method
        trait definition substitution bodyInstance)
      (callee_assembled : EvidenceEnvironment.AssembledFrom callerEvidence
        (closedEvidence :: methodEvidence.map Prod.snd)
        ((methodAssumptions trait implementation method).map
          (ProgramPredicate.applyParameters substitution)) calleeEvidence)
      (callee_covers : calleeEvidence.Covers bodyInstance.context) :
      OperatorMethodSelected program context callerEvidence traitName methodName
        (primary :: methodRequirements) bodyInstance calleeEvidence

/-- Statement-only root extraction. -/
inductive StatementRoots : List NodeId → List StatementId → Prop where
  | nil : StatementRoots [] []
  | cons {id : StatementId} {roots : List NodeId}
      {statements : List StatementId}
      (tail : StatementRoots roots statements) :
      StatementRoots (.statement id :: roots) (id :: statements)

/-- Allocate source binders left-to-right, extending the lexical environment
with the most recent binder at the head. -/
inductive BindersAllocate : Environment → Heap →
    List TypedBinder → List Value → Environment → Heap → Prop where
  | nil (environment : Environment) (heap : Heap) :
      BindersAllocate environment heap [] [] environment heap
  | cons
      {environment finalEnvironment : Environment}
      {heap nextHeap finalHeap : Heap}
      {binder : TypedBinder} {binders : List TypedBinder}
      {value : Value} {values : List Value} {location : Location}
      (allocation : Heap.Allocates heap binder.scheme.body (some value)
        location nextHeap)
      (tail : BindersAllocate ((binder.id, location) :: environment) nextHeap
        binders values finalEnvironment finalHeap) :
      BindersAllocate environment heap (binder :: binders) (value :: values)
        finalEnvironment finalHeap

/-- Compound assignment reuses the selected pre-RHS leaf. -/
inductive AssignmentValueApplies : Syntax.ValueAssignOp →
    Option Value → Value → Value → Prop where
  | equal (previous : Option Value) (right : Value) :
      AssignmentValueApplies .equal previous right right
  | add {left right result : Value}
      (applies : BinaryPrimitiveApplies .add left right result) :
      AssignmentValueApplies .add (some left) right result
  | subtract {left right result : Value}
      (applies : BinaryPrimitiveApplies .subtract left right result) :
      AssignmentValueApplies .subtract (some left) right result
  | multiply {left right result : Value}
      (applies : BinaryPrimitiveApplies .multiply left right result) :
      AssignmentValueApplies .multiply (some left) right result
  | divide {left right result : Value}
      (applies : BinaryPrimitiveApplies .divide left right result) :
      AssignmentValueApplies .divide (some left) right result
  | modulo {left right result : Value}
      (applies : BinaryPrimitiveApplies .modulo left right result) :
      AssignmentValueApplies .modulo (some left) right result
  | bitAnd {left right result : Value}
      (applies : BinaryPrimitiveApplies .bitAnd left right result) :
      AssignmentValueApplies .bitAnd (some left) right result
  | bitXor {left right result : Value}
      (applies : BinaryPrimitiveApplies .bitXor left right result) :
      AssignmentValueApplies .bitXor (some left) right result
  | bitOr {left right result : Value}
      (applies : BinaryPrimitiveApplies .bitOr left right result) :
      AssignmentValueApplies .bitOr (some left) right result

/-- Bit-not assignment operates on the leaf snapshot captured by place
resolution. -/
inductive BitNotSnapshot : Option Value → Value → Prop where
  | word (value : Core.Word) :
      BitNotSnapshot (some (.word value)) (.word value.bitNot)

/-- Restore a scoped control result to its entry environment. -/
def restoreControl (outer : Environment) : ControlOutcome → ControlOutcome
  | .fallthrough _ => .fallthrough outer
  | .returned value => .returned value
  | .breaking _ => .breaking outer
  | .continuing _ => .continuing outer
  | .fault reason => .fault reason

/-- Results which stop ordinary statement sequencing. -/
inductive TerminalControl : ControlOutcome → Prop where
  | returned (value : Value) : TerminalControl (.returned value)
  | breaking (environment : Environment) : TerminalControl (.breaking environment)
  | continuing (environment : Environment) : TerminalControl (.continuing environment)
  | fault (reason : SemanticFault) : TerminalControl (.fault reason)

/-- Ordinary occurrences place their own evidence before every output-path
requirement. -/
def OrdinaryRequirementLayout (requirements : List RequirementId)
    (coercions : List CoercionStep) (owned : List RequirementId) : Prop :=
  requirements = owned ++ coercionRequirementIds coercions

/-- Direct calls interleave selected-result coercions, declaration evidence,
and contextual-result coercions exactly as retained by source inference. -/
inductive DirectCallProducesEvidence (context : Context)
    (callerEvidence : EvidenceEnvironment)
    (requirements : List RequirementId) (coercions : List CoercionStep)
    (predicates : List ProgramPredicate) : EvidenceEnvironment → Prop where
  | intro
      {selected contextual : List CoercionStep}
      {signatureRequirements : List RequirementId}
      {calleeEvidence : EvidenceEnvironment}
      (coercions_eq : coercions = selected ++ contextual)
      (requirements_eq : requirements =
        coercionRequirementIds selected ++
          (signatureRequirements ++ coercionRequirementIds contextual))
      (produces : RequirementsProduceEnvironment context callerEvidence
        signatureRequirements predicates calleeEvidence) :
      DirectCallProducesEvidence context callerEvidence requirements coercions
        predicates calleeEvidence

/-- A closure invocation frame recovers the static source context needed to
interpret retained requirement identities and closes all of its generic
assumptions.  Dynamic dispatch only needs identity uniqueness here; evidence
validity is supplied by the typing derivation at each use site. -/
structure ClosureFrame (program : Program) (function : Closure) : Prop where
  signatures : function.context.signatures = program.signatures
  owner : function.context.currentDeclaration = some function.source.owner
  code : ClosureCodeValid function.context function
  requirements : RequirementIdsUnique function.context
  evidence_covers : function.evidence.Covers function.context

/-- A selected match branch after its pattern bindings have been allocated. -/
inductive MatchBranchExecutes
    (ExecuteStatements : Environment → Heap →
      List StatementId → ControlOutcome → Heap → Prop)
    (entryEnvironment : Environment) :
    Heap → MatchCaseSelection → ControlOutcome → Heap → Prop where
  | arm
      {before bound final : Heap} {body : List StatementId}
      {bindings : List (TypedBinder × Value)}
      {binders : List TypedBinder} {values : List Value}
      {armEnvironment : Environment} {outcome : ControlOutcome}
      (binders_eq : binders = bindings.map Prod.fst)
      (values_eq : values = bindings.map Prod.snd)
      (allocate : BindersAllocate entryEnvironment before binders values
        armEnvironment bound)
      (execute : ExecuteStatements armEnvironment bound body outcome final) :
      MatchBranchExecutes ExecuteStatements entryEnvironment before
        (.arm body bindings) (restoreControl entryEnvironment outcome) final
  | default
      {before final : Heap} {body : List StatementId}
      {outcome : ControlOutcome}
      (execute : ExecuteStatements entryEnvironment before body outcome final) :
      MatchBranchExecutes ExecuteStatements entryEnvironment before
        (.default body) (restoreControl entryEnvironment outcome) final
  | noBranch {heap : Heap} :
      MatchBranchExecutes ExecuteStatements entryEnvironment heap
        .noBranch (.fallthrough entryEnvironment) heap

set_option maxHeartbeats 1200000 in
mutual

  /-- Evaluate one expression occurrence and then execute its retained output
  coercion path. -/
  inductive ExpressionEvaluates (program : Program) :
      Context → EvidenceEnvironment → TypedSource → Environment →
        Heap → ExpressionId → Value → Heap → Prop where
    | intro
        {context : Context} {evidence : EvidenceEnvironment}
        {source : TypedSource} {environment : Environment}
        {before middle after : Heap} {id : ExpressionId}
        {node : ExpressionNode} {raw result : Value}
        (contains : ContainsExpression source id node)
        (form : ExpressionFormEvaluates program context evidence source
          environment before node.form node.requirements node.coercions raw middle)
        (coercions : CoercionPathExecutes program context evidence middle
          node.coercions raw result after) :
        ExpressionEvaluates program context evidence source environment before
          id result after
    | generalizedLocal
        {context : Context} {evidence : EvidenceEnvironment}
        {source : TypedSource} {environment : Environment}
        {before after : Heap} {id : ExpressionId}
        {node : ExpressionNode} {name : String} {binder : Resolved.LocalId}
        {owned : List RequirementId} {location : Location} {cell : Cell}
        {function : GeneralizedClosure} {substitution : Substitution}
        {produced : EvidenceEnvironment} {value : Value}
        (contains : ContainsExpression source id node)
        (form_eq : node.form = .reference name (.local binder))
        (layout : OrdinaryRequirementLayout node.requirements node.coercions
          owned)
        (lookup : Environment.LooksUp environment binder location)
        (read : Heap.Reads before location cell)
        (descriptor : cell.generalized = some function)
        (context_fields : RuntimeContextFields function.definitionContext
          context)
        (instantiation : LocalSchemeRuntimeInstantiation context evidence
          function.binder node.rawType owned substitution produced)
        (coercions : CoercionPathExecutes program context evidence before
          node.coercions
          (.closure (function.instantiate substitution
            (produced ++ evidence.applySubstitution substitution)))
          value after) :
        ExpressionEvaluates program context evidence source environment before
          id value after

  /-- Raw evaluation of every resolved expression form. -/
  inductive ExpressionFormEvaluates (program : Program) :
      Context → EvidenceEnvironment → TypedSource → Environment →
        Heap → ExpressionForm → List RequirementId →
        List CoercionStep → Value → Heap → Prop where
    | literal
        {context evidence source environment heap literal requirements coercions
          value}
        (layout : OrdinaryRequirementLayout requirements coercions [])
        (constructs : LiteralConstructs literal value) :
        ExpressionFormEvaluates program context evidence source environment heap
          (.literal literal) requirements coercions value heap
    | integerLiteral
        {context evidence source environment heap literal resolution requirements
          coercions value}
        (layout : OrdinaryRequirementLayout requirements coercions
          [resolution.requirement])
        (constructs : ResolvedIntegerLiteralConstructs context literal resolution
          value) :
        ExpressionFormEvaluates program context evidence source environment heap
          (.integerLiteral literal resolution) requirements coercions value heap
    | local
        {context evidence source environment heap name binder requirements coercions
          location cell value}
        (layout : OrdinaryRequirementLayout requirements coercions [])
        (lookup : Environment.LooksUp environment binder location)
        (read : Heap.Reads heap location cell)
        (descriptor_empty : cell.generalized = none)
        (initialized : cell.value = some value) :
        ExpressionFormEvaluates program context evidence source environment heap
          (.reference name (.local binder)) requirements coercions value heap
    | localEmptyMapping
        {context evidence source environment before after name binder requirements
          coercions location cell keyType valueType}
        (layout : OrdinaryRequirementLayout requirements coercions [])
        (lookup : Environment.LooksUp environment binder location)
        (read : Heap.Reads before location cell)
        (descriptor_empty : cell.generalized = none)
        (type_eq : cell.type = .mapping keyType valueType)
        (empty : cell.value = none)
        (write : Heap.Writes before location
          (some (.mapping keyType valueType [])) after) :
        ExpressionFormEvaluates program context evidence source environment before
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
        ExpressionFormEvaluates program context evidence source environment heap
          (.reference name (.declaration instantiation)) requirements coercions
          (.global ⟨instantiation, produced⟩) heap
    | builtinFunction
        {context evidence source environment heap name function requirements
          coercions}
        (layout : OrdinaryRequirementLayout requirements coercions []) :
        ExpressionFormEvaluates program context evidence source environment heap
          (.reference name (.builtinFunction function)) requirements coercions
          (.builtin ⟨function⟩) heap
    | builtinBoolean
        {context evidence source environment heap name value requirements coercions}
        (layout : OrdinaryRequirementLayout requirements coercions []) :
        ExpressionFormEvaluates program context evidence source environment heap
          (.reference name (.builtinBoolean value)) requirements coercions
          (.bool value) heap
    | group
        {context evidence source environment before after inner requirements
          coercions value}
        (layout : OrdinaryRequirementLayout requirements coercions [])
        (inner_evaluates : ExpressionEvaluates program context evidence source
          environment before inner value after) :
        ExpressionFormEvaluates program context evidence source environment before
          (.group inner) requirements coercions value after
    | tuple
        {context evidence source environment before after elements requirements
          coercions values packed}
        (layout : OrdinaryRequirementLayout requirements coercions [])
        (elements_evaluate : ExpressionsEvaluate program context evidence source
          environment before elements values after)
        (pack : ValuesPack values packed) :
        ExpressionFormEvaluates program context evidence source environment before
          (.tuple elements) requirements coercions packed after
    | unary
        {context evidence source environment before middle after operator operand
          requirements coercions owned input output}
        (layout : OrdinaryRequirementLayout requirements coercions owned)
        (operand_evaluates : ExpressionEvaluates program context evidence source
          environment before operand input middle)
        (applies : UnaryOperationApplies program context evidence middle operator
          owned input output after) :
        ExpressionFormEvaluates program context evidence source environment before
          (.unary operator operand) requirements coercions output after
    | binaryShortCircuit
        {context evidence source environment before after left operator right
          requirements coercions owned leftValue result}
        (layout : OrdinaryRequirementLayout requirements coercions owned)
        (left_evaluates : ExpressionEvaluates program context evidence source
          environment before left leftValue after)
        (circuit : ShortCircuits operator leftValue result)
        (owned_empty : owned = []) :
        ExpressionFormEvaluates program context evidence source environment before
          (.binary left operator right) requirements coercions result after
    | binaryEvaluateRight
        {context evidence source environment before leftHeap rightHeap after
          left operator right requirements coercions owned leftValue rightValue
          result}
        (layout : OrdinaryRequirementLayout requirements coercions owned)
        (left_evaluates : ExpressionEvaluates program context evidence source
          environment before left leftValue leftHeap)
        (evaluate_right : EvaluatesRightOperand operator leftValue)
        (right_evaluates : ExpressionEvaluates program context evidence source
          environment leftHeap right rightValue rightHeap)
        (applies : BinaryOperationApplies program context evidence rightHeap
          operator owned leftValue rightValue result after) :
        ExpressionFormEvaluates program context evidence source environment before
          (.binary left operator right) requirements coercions result after
    | conditionalTrue
        {context evidence source environment before middle after condition
          thenBranch elseBranch requirements coercions value}
        (layout : OrdinaryRequirementLayout requirements coercions [])
        (condition_evaluates : ExpressionEvaluates program context evidence source
          environment before condition (.bool true) middle)
        (branch_evaluates : ExpressionEvaluates program context evidence source
          environment middle thenBranch value after) :
        ExpressionFormEvaluates program context evidence source environment before
          (.conditional condition thenBranch elseBranch) requirements coercions
          value after
    | conditionalFalse
        {context evidence source environment before middle after condition
          thenBranch elseBranch requirements coercions value}
        (layout : OrdinaryRequirementLayout requirements coercions [])
        (condition_evaluates : ExpressionEvaluates program context evidence source
          environment before condition (.bool false) middle)
        (branch_evaluates : ExpressionEvaluates program context evidence source
          environment middle elseBranch value after) :
        ExpressionFormEvaluates program context evidence source environment before
          (.conditional condition thenBranch elseBranch) requirements coercions
          value after
    | lambda
        {context evidence source environment heap parameters returnType body
          requirements coercions}
        (layout : OrdinaryRequirementLayout requirements coercions []) :
        ExpressionFormEvaluates program context evidence source environment heap
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
        (arguments_evaluate : ExpressionsEvaluate program context evidence source
          environment before arguments argumentValues argumentsHeap)
        (call_evidence : DirectCallProducesEvidence context evidence requirements
          coercions instantiation.predicates calleeEvidence)
        (applies : CallableApplies program context evidence calleeEvidence
          argumentsHeap (.global ⟨instantiation, calleeEvidence⟩)
          argumentValues result after) :
        ExpressionFormEvaluates program context evidence source environment before
          (.call callee arguments (.declaration instantiation)) requirements
          coercions result after
    | builtinCall
        {context evidence source environment before argumentsHeap after
          callee arguments function requirements coercions argumentValues result}
        (layout : OrdinaryRequirementLayout requirements coercions [])
        (arguments_evaluate : ExpressionsEvaluate program context evidence source
          environment before arguments argumentValues argumentsHeap)
        (applies : CallableApplies program context evidence [] argumentsHeap
          (.builtin ⟨function⟩) argumentValues result after) :
        ExpressionFormEvaluates program context evidence source environment before
          (.call callee arguments (.builtinFunction function)) requirements
          coercions result after
    | indirectCall
        {context evidence source environment before calleeHeap argumentHeap
          coercedHeap after callee arguments metadata requirements coercions
          callable argumentValues packed coerced appliedArguments result
          invocationEvidence}
        (requirements_eq : requirements =
          coercionRequirementIds metadata.argumentCoercions ++
            coercionRequirementIds coercions)
        (callee_evaluates : ExpressionEvaluates program context evidence source
          environment before callee callable calleeHeap)
        (arguments_evaluate : ExpressionsEvaluate program context evidence source
          environment calleeHeap arguments argumentValues argumentHeap)
        (pack_before : ValuesPack argumentValues packed)
        (argument_coercions : CoercionPathExecutes program context evidence
          argumentHeap metadata.argumentCoercions packed coerced coercedHeap)
        (pack_after : ValuesPack appliedArguments coerced)
        (source_arity : arguments.length = metadata.argumentCount)
        (applied_arity : appliedArguments.length = metadata.argumentCount)
        (applies : CallableApplies program context evidence invocationEvidence coercedHeap
          callable appliedArguments result after) :
        ExpressionFormEvaluates program context evidence source environment before
          (.call callee arguments (.indirect metadata)) requirements coercions
          result after
    | constructor
        {context evidence source environment before after instantiation arguments
          requirements coercions values}
        (layout : OrdinaryRequirementLayout requirements coercions [])
        (valid : DataConstructorInstantiation.Valid context instantiation)
        (arguments_evaluate : ExpressionsEvaluate program context evidence source
          environment before arguments values after) :
        ExpressionFormEvaluates program context evidence source environment before
          (.constructor instantiation arguments) requirements coercions
          (.constructed instantiation values) after
    | member
        {context evidence source environment before after base name index
          requirements coercions instantiation arguments selected}
        (layout : OrdinaryRequirementLayout requirements coercions [])
        (base_evaluates : ExpressionEvaluates program context evidence source
          environment before base (.constructed instantiation arguments) after)
        (selected_at : ValueAt arguments index selected) :
        ExpressionFormEvaluates program context evidence source environment before
          (.member base name index) requirements coercions selected after
    | proxy
        {context evidence source environment heap inner requirements coercions}
        (layout : OrdinaryRequirementLayout requirements coercions []) :
        ExpressionFormEvaluates program context evidence source environment heap
          (.proxy inner) requirements coercions (.proxy inner) heap
    | indexFound
        {context evidence source environment before middle after base index
          requirements coercions keyType valueType entries key value}
        (layout : OrdinaryRequirementLayout requirements coercions [])
        (base_evaluates : ExpressionEvaluates program context evidence source
          environment before base (.mapping keyType valueType entries) middle)
        (index_evaluates : ExpressionEvaluates program context evidence source
          environment middle index key after)
        (lookup : MappingLookup key entries value) :
        ExpressionFormEvaluates program context evidence source environment before
          (.index base index) requirements coercions value after
    | indexDefault
        {context evidence source environment before middle after base index
          requirements coercions keyType valueType entries key value}
        (layout : OrdinaryRequirementLayout requirements coercions [])
        (base_evaluates : ExpressionEvaluates program context evidence source
          environment before base (.mapping keyType valueType entries) middle)
        (index_evaluates : ExpressionEvaluates program context evidence source
          environment middle index key after)
        (absent : MappingAbsent key entries)
        (defaulted : DefaultValue valueType value) :
        ExpressionFormEvaluates program context evidence source environment before
          (.index base index) requirements coercions value after

  /-- Left-to-right evaluation of an expression vector. -/
  inductive ExpressionsEvaluate (program : Program) :
      Context → EvidenceEnvironment → TypedSource → Environment →
        Heap → List ExpressionId → List Value → Heap → Prop where
    | nil
        {context evidence source environment heap} :
        ExpressionsEvaluate program context evidence source environment heap [] []
          heap
    | cons
        {context evidence source environment before middle after expression
          expressions value values}
        (head : ExpressionEvaluates program context evidence source environment
          before expression value middle)
        (tail : ExpressionsEvaluate program context evidence source environment
          middle expressions values after) :
        ExpressionsEvaluate program context evidence source environment before
          (expression :: expressions) (value :: values) after

  /-- Place-index evaluation specialized to the mutually recursive source
  expression judgment. -/
  inductive SourceProjectionsEvaluate (program : Program) :
      Context → EvidenceEnvironment → TypedSource → Environment → Heap →
        List PlaceProjection → List EvaluatedProjection → Heap → Prop where
    | nil
        {context evidence source environment heap} :
        SourceProjectionsEvaluate program context evidence source environment heap
          [] [] heap
    | member
        {context evidence source environment before after name index projections
          evaluated}
        (tail : SourceProjectionsEvaluate program context evidence source environment
          before projections evaluated after) :
        SourceProjectionsEvaluate program context evidence source environment before
          (.member name index :: projections)
          (.member name index :: evaluated) after
    | index
        {context evidence source environment before middle after expression key
          projections evaluated}
        (head : ExpressionEvaluates program context evidence source environment
          before expression key middle)
        (tail : SourceProjectionsEvaluate program context evidence source environment
          middle projections evaluated after) :
        SourceProjectionsEvaluate program context evidence source environment before
          (.index expression :: projections) (.index key :: evaluated) after

  /-- Resolve one source place after evaluating every index exactly once. -/
  inductive SourcePlaceResolves (program : Program) :
      Context → EvidenceEnvironment → TypedSource → Environment → Heap →
        PlaceResolution → ResolvedPlace → Heap → Prop where
    | intro
        {context evidence source environment before after place location initialCell
          currentCell evaluated initial selected}
        (root_lookup : Environment.LooksUp environment place.root location)
        (initial_read : Heap.Reads before location initialCell)
        (evaluate : SourceProjectionsEvaluate program context evidence source
          environment before place.projections evaluated after)
        (current_read : Heap.Reads after location currentCell)
        (initial_value : RootInitialValue currentCell initial)
        (selection : ProjectionsRead initial evaluated selected) :
        SourcePlaceResolves program context evidence source environment before place
          { location := location
            rootType := currentCell.type
            valueType := place.type
            projections := evaluated
            selected := selected }
          after

  /-- Full target-before-RHS assignment transaction, specialized to source
  expression evaluation. -/
  inductive SourcePlaceAssignment (program : Program) :
      Context → EvidenceEnvironment → TypedSource →
        (Option Value → Value → Value → Prop) →
        Environment → Heap → PlaceResolution → ExpressionId →
        Value → Heap → Prop where
    | intro
        {context evidence source combine environment before targetHeap rhsHeap after
          place target rightExpression rightValue updatedRoot}
        (resolve : SourcePlaceResolves program context evidence source environment
          before place target targetHeap)
        (evaluate_right : ExpressionEvaluates program context evidence source
          environment targetHeap rightExpression rightValue rhsHeap)
        (write : ResolvedPlaceWrites
          (fun _ updated => combine target.selected rightValue updated)
          rhsHeap target updatedRoot after) :
        SourcePlaceAssignment program context evidence source combine environment
          before place rightExpression updatedRoot after

  /-- Snapshot-only place update used by unary assignment forms. -/
  inductive SourcePlaceSnapshotUpdate (program : Program) :
      Context → EvidenceEnvironment → TypedSource →
        (Option Value → Value → Prop) → Environment → Heap →
        PlaceResolution → Value → Heap → Prop where
    | intro
        {context evidence source modify environment before selectedHeap after place
          target updatedRoot}
        (resolve : SourcePlaceResolves program context evidence source environment
          before place target selectedHeap)
        (write : ResolvedPlaceWrites
          (fun _ updated => modify target.selected updated)
          selectedHeap target updatedRoot after) :
        SourcePlaceSnapshotUpdate program context evidence source modify environment
          before place updatedRoot after

  /-- Primitive or evidence-selected unary operation. -/
  inductive UnaryOperationApplies (program : Program) :
      Context → EvidenceEnvironment → Heap → Syntax.UnaryOp →
        List RequirementId → Value → Value → Heap → Prop where
    | primitive
        {context evidence heap operator input output}
        (applies : UnaryPrimitiveApplies operator input output) :
        UnaryOperationApplies program context evidence heap operator [] input
          output heap
    | method
        {context evidence before after operator input output requirements
          traitName methodName bodyInstance calleeEvidence}
        (dispatch : UnaryTraitDispatch operator traitName methodName)
        (selected : OperatorMethodSelected program context evidence traitName
          methodName requirements bodyInstance calleeEvidence)
        (invokes : BodyInvokes program bodyInstance calleeEvidence before [input]
          output after) :
        UnaryOperationApplies program context evidence before operator requirements
          input output after

  /-- Primitive or evidence-selected strict binary operation. -/
  inductive BinaryOperationApplies (program : Program) :
      Context → EvidenceEnvironment → Heap → Syntax.BinaryOp →
        List RequirementId → Value → Value → Value → Heap → Prop where
    | primitive
        {context evidence heap operator left right output}
        (applies : BinaryPrimitiveApplies operator left right output) :
        BinaryOperationApplies program context evidence heap operator [] left right
          output heap
    | method
        {context evidence before after operator left right output requirements
          traitName methodName bodyInstance calleeEvidence}
        (dispatch : BinaryTraitDispatch operator traitName methodName)
        (selected : OperatorMethodSelected program context evidence traitName
          methodName requirements bodyInstance calleeEvidence)
        (invokes : BodyInvokes program bodyInstance calleeEvidence before
          [left, right] output after) :
        BinaryOperationApplies program context evidence before operator requirements
          left right output after

  /-- One evidence-checked coercion edge, either compiler-provided or backed by
  a selected source `coerce` method. -/
  inductive CoercionStepExecutes (program : Program) :
      Context → EvidenceEnvironment → Heap → CoercionStep →
        Value → Value → Heap → Prop where
    | primitive
        {context evidence heap step input output}
        (no_source_method : ∀ bodyInstance calleeEvidence,
          ¬ OperatorMethodSelected program context evidence "Coerce" "coerce"
            step.requirements bodyInstance calleeEvidence)
        (applies : CoercionApplies context step input output) :
        CoercionStepExecutes program context evidence heap step input output heap
    | method
        {context evidence before after step input output bodyInstance calleeEvidence}
        (selected : OperatorMethodSelected program context evidence "Coerce"
          "coerce" step.requirements bodyInstance calleeEvidence)
        (invokes : BodyInvokes program bodyInstance calleeEvidence before [input]
          output after) :
        CoercionStepExecutes program context evidence before step input output after

  /-- Left-to-right execution of a retained coercion path. -/
  inductive CoercionPathExecutes (program : Program) :
      Context → EvidenceEnvironment → Heap → List CoercionStep →
        Value → Value → Heap → Prop where
    | nil
        {context evidence heap value} :
        CoercionPathExecutes program context evidence heap [] value value heap
    | cons
        {context evidence before middle after step steps input converted output}
        (head : CoercionStepExecutes program context evidence before step input
          converted middle)
        (tail : CoercionPathExecutes program context evidence middle steps converted
          output after) :
        CoercionPathExecutes program context evidence before (step :: steps) input
          output after

  /-- Application of a first-class closure, global declaration, or builtin. -/
  inductive CallableApplies (program : Program) :
      Context → EvidenceEnvironment → EvidenceEnvironment → Heap →
        Value → List Value → Value → Heap → Prop where
    | builtin
        {context callerEvidence invocationEvidence heap function arguments result}
        (applies : BuiltinApplies function.id arguments result) :
        CallableApplies program context callerEvidence invocationEvidence heap
          (.builtin function) arguments result heap
    | global
        {context callerEvidence invocationEvidence before after function arguments
          result bodyInstance}
        (instantiates : FunctionInstantiates program function.instantiation
          bodyInstance)
        (invocation_eq : invocationEvidence = function.evidence)
        (covers : invocationEvidence.Covers bodyInstance.context)
        (invokes : BodyInvokes program bodyInstance invocationEvidence before
          arguments result after) :
        CallableApplies program context callerEvidence invocationEvidence before
          (.global function) arguments result after
    | closure
        {context callerEvidence invocationEvidence before bound after function
          arguments environment outcome result parameterTypes callContext
          finalContext}
        (invocation_eq : invocationEvidence = function.evidence)
        (frame : ClosureFrame program function)
        (parameters_extend : MonoBindersExtend function.source.owner
          function.context function.parameters parameterTypes callContext)
        (allocate : BindersAllocate function.captured before function.parameters
          arguments environment bound)
        (execute : FunctionStatementsExecute program callContext function.evidence
          function.source environment bound function.body finalContext outcome after)
        (returned : outcome = .returned result) :
        CallableApplies program context callerEvidence invocationEvidence before
          (.closure function) arguments result after
    | closureUnit
        {context callerEvidence invocationEvidence before bound after function
          arguments environment outcome parameterTypes callContext finalContext}
        (invocation_eq : invocationEvidence = function.evidence)
        (frame : ClosureFrame program function)
        (result_unit : function.resultType = .unit)
        (parameters_extend : MonoBindersExtend function.source.owner
          function.context function.parameters parameterTypes callContext)
        (allocate : BindersAllocate function.captured before function.parameters
          arguments environment bound)
        (execute : FunctionStatementsExecute program callContext function.evidence
          function.source environment bound function.body finalContext outcome after)
        (fell_through : ∃ finalEnvironment,
          outcome = .fallthrough finalEnvironment) :
        CallableApplies program context callerEvidence invocationEvidence before
          (.closure function) arguments .unit after

  /-- Invoke an instantiated catalog body from an empty lexical frame. -/
  inductive BodyInvokes (program : Program) :
      BodyInstance → EvidenceEnvironment → Heap → List Value →
        Value → Heap → Prop where
    | returned
        {bodyInstance evidence before bound after arguments environment roots result
          outcome inputTypes lexicalContext finalContext}
        (covers : evidence.Covers bodyInstance.context)
        (roots_eq : StatementRoots bodyInstance.source.roots roots)
        (inputs_extend : MonoBindersExtend bodyInstance.source.owner
          bodyInstance.context bodyInstance.source.inputs inputTypes lexicalContext)
        (allocate : BindersAllocate [] before bodyInstance.source.inputs arguments
          environment bound)
        (execute : FunctionStatementsExecute program lexicalContext evidence
          bodyInstance.source environment bound roots finalContext outcome after)
        (returned : outcome = .returned result) :
        BodyInvokes program bodyInstance evidence before arguments result after
    | unit
        {bodyInstance evidence before bound after arguments environment roots
          outcome inputTypes lexicalContext finalContext}
        (covers : evidence.Covers bodyInstance.context)
        (result_unit : bodyInstance.resultType = .unit)
        (roots_eq : StatementRoots bodyInstance.source.roots roots)
        (inputs_extend : MonoBindersExtend bodyInstance.source.owner
          bodyInstance.context bodyInstance.source.inputs inputTypes lexicalContext)
        (allocate : BindersAllocate [] before bodyInstance.source.inputs arguments
          environment bound)
        (execute : FunctionStatementsExecute program lexicalContext evidence
          bodyInstance.source environment bound roots finalContext outcome after)
        (fell_through : ∃ finalEnvironment,
          outcome = .fallthrough finalEnvironment) :
        BodyInvokes program bodyInstance evidence before arguments .unit after

  /-- Execute one statement occurrence.  Ordinary binders store an optional
  value at the monomorphic scheme body.  A canonical generalized direct-lambda
  initializer instead stores its principal closure descriptor without first
  evaluating the initializer at any one instantiation. -/
  inductive StatementExecutes (program : Program) :
      Context → EvidenceEnvironment → TypedSource → Environment →
        Heap → StatementId → Context → ControlOutcome → Heap → Prop where
    | letUninitialized
        {context finalContext evidence source environment before after id node binder
          location}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .letDecl binder none)
        (monomorphic : binder.scheme.quantified = [])
        (extension : BinderExtends source.owner context binder finalContext)
        (allocate : Heap.Allocates before binder.scheme.body none location after) :
        StatementExecutes program context evidence source environment before id
          finalContext (.fallthrough ((binder.id, location) :: environment)) after
    | letInitialized
        {context finalContext evidence source environment before middle after id node
          binder initializer value location}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .letDecl binder (some initializer))
        (evaluate : ExpressionEvaluates program context evidence source environment
          before initializer value middle)
        (monomorphic : binder.scheme.quantified = [])
        (extension : BinderExtends source.owner context binder finalContext)
        (allocate : Heap.Allocates middle binder.scheme.body (some value) location
          after) :
        StatementExecutes program context evidence source environment before id
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
        StatementExecutes program context evidence source environment before id
          finalContext (.fallthrough ((binder.id, location) :: environment)) after
    | returnUnit
        {context evidence source environment heap id node}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .returnStmt none) :
        StatementExecutes program context evidence source environment heap id
          context (.returned .unit) heap
    | returnValue
        {context evidence source environment before after id node expression value}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .returnStmt (some expression))
        (evaluate : ExpressionEvaluates program context evidence source environment
          before expression value after) :
        StatementExecutes program context evidence source environment before id
          context (.returned value) after
    | expression
        {context evidence source environment before after id node expression
          semicolon value}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .expression expression semicolon)
        (evaluate : ExpressionEvaluates program context evidence source environment
          before expression value after) :
        StatementExecutes program context evidence source environment before id
          context (.fallthrough environment) after
    | assignValue
        {context evidence source environment before after id node assignment
          operator rhs updatedRoot}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .assignValue assignment operator rhs)
        (assignment_executes : SourcePlaceAssignment program context evidence source
          (AssignmentValueApplies operator) environment before assignment.target rhs
          updatedRoot after) :
        StatementExecutes program context evidence source environment before id
          context (.fallthrough environment) after
    | assignBitNot
        {context evidence source environment before after id node assignment
          updatedRoot}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .assignBitNot assignment)
        (assignment_executes : SourcePlaceSnapshotUpdate program context evidence
          source BitNotSnapshot environment before assignment.target updatedRoot
          after) :
        StatementExecutes program context evidence source environment before id
          context (.fallthrough environment) after
    | ifTrue
        {context evidence source environment before middle after id node condition
          thenBody elseBody innerFinalContext outcome}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .ifThen condition thenBody elseBody)
        (condition_evaluates : ExpressionEvaluates program context evidence source
          environment before condition (.bool true) middle)
        (body_executes : StatementsExecute program context evidence source
          environment middle thenBody innerFinalContext outcome after) :
        StatementExecutes program context evidence source environment before id
          context (restoreControl environment outcome) after
    | ifFalseWithoutElse
        {context evidence source environment before after id node condition thenBody}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .ifThen condition thenBody none)
        (condition_evaluates : ExpressionEvaluates program context evidence source
          environment before condition (.bool false) after) :
        StatementExecutes program context evidence source environment before id
          context (.fallthrough environment) after
    | ifFalseWithElse
        {context evidence source environment before middle after id node condition
          thenBody elseBody innerFinalContext outcome}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .ifThen condition thenBody (some elseBody))
        (condition_evaluates : ExpressionEvaluates program context evidence source
          environment before condition (.bool false) middle)
        (body_executes : StatementsExecute program context evidence source
          environment middle elseBody innerFinalContext outcome after) :
        StatementExecutes program context evidence source environment before id
          context (restoreControl environment outcome) after
    | block
        {context evidence source environment before after id node body
          innerFinalContext outcome}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .block body)
        (body_executes : StatementsExecute program context evidence source
          environment before body innerFinalContext outcome after) :
        StatementExecutes program context evidence source environment before id
          context (restoreControl environment outcome) after
    | matchArm
        {context evidence source environment before scrutineeHeap hiddenHeap after
          id node resolution scrutinee scrutineeNode location armBody bindings
          binders values armContext armFinalContext armEnvironment bound outcome}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .matchWith resolution)
        (scrutinee_contains : ContainsExpression source resolution.scrutinee
          scrutineeNode)
        (scrutinee_evaluates : ExpressionEvaluates program context evidence source
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
        (execute : StatementsExecute program armContext evidence source armEnvironment
          bound armBody armFinalContext outcome after) :
        StatementExecutes program context evidence source environment before id
          context (restoreControl environment outcome) after
    | matchDefault
        {context evidence source environment before scrutineeHeap hiddenHeap after
          id node resolution scrutinee scrutineeNode location defaultBody
          defaultFinalContext outcome}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .matchWith resolution)
        (scrutinee_contains : ContainsExpression source resolution.scrutinee
          scrutineeNode)
        (scrutinee_evaluates : ExpressionEvaluates program context evidence source
          environment before resolution.scrutinee scrutinee scrutineeHeap)
        (allocate_hidden : Heap.Allocates scrutineeHeap scrutineeNode.type
          (some scrutinee) location hiddenHeap)
        (select : MatchCasesSelect context scrutinee resolution.cases
          resolution.defaultBody (.default defaultBody))
        (execute : StatementsExecute program context evidence source environment
          hiddenHeap defaultBody defaultFinalContext outcome after) :
        StatementExecutes program context evidence source environment before id
          context (restoreControl environment outcome) after
    | matchNoBranch
        {context evidence source environment before scrutineeHeap hiddenHeap id node
          resolution scrutinee scrutineeNode location}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .matchWith resolution)
        (scrutinee_contains : ContainsExpression source resolution.scrutinee
          scrutineeNode)
        (scrutinee_evaluates : ExpressionEvaluates program context evidence source
          environment before resolution.scrutinee scrutinee scrutineeHeap)
        (allocate_hidden : Heap.Allocates scrutineeHeap scrutineeNode.type
          (some scrutinee) location hiddenHeap)
        (select : MatchCasesSelect context scrutinee resolution.cases
          resolution.defaultBody .noBranch) :
        StatementExecutes program context evidence source environment before id
          context (.fallthrough environment) hiddenHeap
    | forLoop
        {context evidence source environment before initialized after id node
          initializer condition post body loopContext loopFinalContext loopEnvironment
          outcome}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .forLoop initializer condition post body)
        (initializer_executes : ForItemsExecute program context evidence source
          environment before initializer loopContext loopEnvironment initialized)
        (iterate : ForLoopExecutes program loopContext evidence source loopEnvironment
          initialized condition post body loopFinalContext outcome after) :
        StatementExecutes program context evidence source environment before id
          context (restoreControl environment outcome) after
    | whileLoop
        {context evidence source environment before after id node condition body
          finalContext outcome}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .whileLoop condition body)
        (iterate : WhileExecutes program context evidence source environment before
          condition body finalContext outcome after) :
        StatementExecutes program context evidence source environment before id
          context (restoreControl environment outcome) after
    | breakStmt
        {context evidence source environment heap id node}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .breakStmt) :
        StatementExecutes program context evidence source environment heap id
          context (.breaking environment) heap
    | continueStmt
        {context evidence source environment heap id node}
        (contains : ContainsStatement source id node)
        (form_eq : node.form = .continueStmt) :
        StatementExecutes program context evidence source environment heap id
          context (.continuing environment) heap

  /-- Source-ordered statement execution with lexical-environment threading. -/
  inductive StatementsExecute (program : Program) :
      Context → EvidenceEnvironment → TypedSource → Environment →
        Heap → List StatementId → Context → ControlOutcome → Heap → Prop where
    | nil
        {context evidence source environment heap} :
        StatementsExecute program context evidence source environment heap []
          context (.fallthrough environment) heap
    | cons
        {context middleContext finalContext evidence source environment before
          middle after statement statements nextEnvironment outcome}
        (head : StatementExecutes program context evidence source environment before
          statement middleContext (.fallthrough nextEnvironment) middle)
        (tail : StatementsExecute program middleContext evidence source
          nextEnvironment middle statements finalContext outcome after) :
        StatementsExecute program context evidence source environment before
          (statement :: statements) finalContext outcome after
    | terminal
        {context finalContext evidence source environment before after statement
          statements outcome}
        (head : StatementExecutes program context evidence source environment before
          statement finalContext outcome after)
        (terminal : TerminalControl outcome) :
        StatementsExecute program context evidence source environment before
          (statement :: statements) finalContext outcome after

  /-- Function-body sequencing adds the source language's final, semicolon-free
  implicit return convention. -/
  inductive FunctionStatementsExecute (program : Program) :
      Context → EvidenceEnvironment → TypedSource → Environment →
        Heap → List StatementId → Context → ControlOutcome → Heap → Prop where
    | nil
        {context evidence source environment heap} :
        FunctionStatementsExecute program context evidence source environment heap
          [] context (.fallthrough environment) heap
    | tailExpression
        {context evidence source environment before after statement node expression
          value}
        (contains : ContainsStatement source statement node)
        (form_eq : node.form = .expression expression false)
        (evaluate : ExpressionEvaluates program context evidence source environment
          before expression value after) :
        FunctionStatementsExecute program context evidence source environment before
          [statement] context (.returned value) after
    | singleton
        {context finalContext evidence source environment before after statement node
          outcome}
        (contains : ContainsStatement source statement node)
        (not_tail : ∀ expression, node.form ≠ .expression expression false)
        (execute : StatementExecutes program context evidence source environment
          before statement finalContext outcome after) :
        FunctionStatementsExecute program context evidence source environment before
          [statement] finalContext outcome after
    | cons
        {context middleContext finalContext evidence source environment before middle
          after statement next rest nextEnvironment outcome}
        (head : StatementExecutes program context evidence source environment before
          statement middleContext (.fallthrough nextEnvironment) middle)
        (tail : FunctionStatementsExecute program middleContext evidence source
          nextEnvironment middle (next :: rest) finalContext outcome after) :
        FunctionStatementsExecute program context evidence source environment before
          (statement :: next :: rest) finalContext outcome after
    | terminal
        {context finalContext evidence source environment before after statement next
          rest outcome}
        (head : StatementExecutes program context evidence source environment before
          statement finalContext outcome after)
        (terminal : TerminalControl outcome) :
        FunctionStatementsExecute program context evidence source environment before
          (statement :: next :: rest) finalContext outcome after

  /-- Execute one canonical `for` header item, using the same ordinary-value or
  generalized-closure allocation boundary as statements. -/
  inductive ForItemExecutes (program : Program) :
      Context → EvidenceEnvironment → TypedSource → Environment →
        Heap → ForItemForm → Context → Environment → Heap → Prop where
    | letUninitialized
        {context finalContext evidence source environment before after binder location}
        (monomorphic : binder.scheme.quantified = [])
        (extension : BinderExtends source.owner context binder finalContext)
        (allocate : Heap.Allocates before binder.scheme.body none location after) :
        ForItemExecutes program context evidence source environment before
          (.letDecl binder none) finalContext
          ((binder.id, location) :: environment) after
    | letInitialized
        {context finalContext evidence source environment before middle after binder
          initializer value location}
        (evaluate : ExpressionEvaluates program context evidence source environment
          before initializer value middle)
        (monomorphic : binder.scheme.quantified = [])
        (extension : BinderExtends source.owner context binder finalContext)
        (allocate : Heap.Allocates middle binder.scheme.body (some value) location
          after) :
        ForItemExecutes program context evidence source environment before
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
        ForItemExecutes program context evidence source environment before
          (.letDecl binder (some initializer)) finalContext
          ((binder.id, location) :: environment) after
    | expression
        {context evidence source environment before after expression value}
        (evaluate : ExpressionEvaluates program context evidence source environment
          before expression value after) :
        ForItemExecutes program context evidence source environment before
          (.expression expression) context environment after
    | assignValue
        {context evidence source environment before after assignment operator rhs
          updatedRoot}
        (execute : SourcePlaceAssignment program context evidence source
          (AssignmentValueApplies operator) environment before assignment.target rhs
          updatedRoot after) :
        ForItemExecutes program context evidence source environment before
          (.assignValue assignment operator rhs) context environment after
    | assignBitNot
        {context evidence source environment before after assignment updatedRoot}
        (execute : SourcePlaceSnapshotUpdate program context evidence source
          BitNotSnapshot environment before assignment.target updatedRoot after) :
        ForItemExecutes program context evidence source environment before
          (.assignBitNot assignment) context environment after

  /-- Left-to-right execution of a `for` header vector. -/
  inductive ForItemsExecute (program : Program) :
      Context → EvidenceEnvironment → TypedSource → Environment →
        Heap → List ForItemForm → Context → Environment → Heap → Prop where
    | nil
        {context evidence source environment heap} :
        ForItemsExecute program context evidence source environment heap []
          context environment heap
    | cons
        {context middleContext finalContext evidence source environment before middle
          after item items nextEnvironment finalEnvironment}
        (head : ForItemExecutes program context evidence source environment before
          item middleContext nextEnvironment middle)
        (tail : ForItemsExecute program middleContext evidence source nextEnvironment
          middle items finalContext finalEnvironment after) :
        ForItemsExecute program context evidence source environment before
          (item :: items) finalContext finalEnvironment after

  /-- Fuel-free execution of a while loop. -/
  inductive WhileExecutes (program : Program) :
      Context → EvidenceEnvironment → TypedSource → Environment →
        Heap → ExpressionId → List StatementId →
        Context → ControlOutcome → Heap → Prop where
    | done
        {context evidence source environment before after condition body}
        (condition_evaluates : ExpressionEvaluates program context evidence source
          environment before condition (.bool false) after) :
        WhileExecutes program context evidence source environment before condition
          body context (.fallthrough environment) after
    | nextFallthrough
        {context evidence source environment before conditionHeap bodyHeap after
          condition body bodyFinalContext bodyEnvironment outcome}
        (condition_evaluates : ExpressionEvaluates program context evidence source
          environment before condition (.bool true) conditionHeap)
        (body_executes : StatementsExecute program context evidence source environment
          conditionHeap body bodyFinalContext (.fallthrough bodyEnvironment) bodyHeap)
        (next : WhileExecutes program context evidence source environment bodyHeap
          condition body context outcome after) :
        WhileExecutes program context evidence source environment before condition
          body context outcome after
    | nextContinue
        {context evidence source environment before conditionHeap bodyHeap after
          condition body bodyFinalContext bodyEnvironment outcome}
        (condition_evaluates : ExpressionEvaluates program context evidence source
          environment before condition (.bool true) conditionHeap)
        (body_executes : StatementsExecute program context evidence source environment
          conditionHeap body bodyFinalContext (.continuing bodyEnvironment) bodyHeap)
        (next : WhileExecutes program context evidence source environment bodyHeap
          condition body context outcome after) :
        WhileExecutes program context evidence source environment before condition
          body context outcome after
    | breaks
        {context evidence source environment before conditionHeap after condition
          body bodyFinalContext bodyEnvironment}
        (condition_evaluates : ExpressionEvaluates program context evidence source
          environment before condition (.bool true) conditionHeap)
        (body_executes : StatementsExecute program context evidence source environment
          conditionHeap body bodyFinalContext (.breaking bodyEnvironment) after) :
        WhileExecutes program context evidence source environment before condition
          body context (.fallthrough environment) after
    | returns
        {context evidence source environment before conditionHeap after condition
          body bodyFinalContext result}
        (condition_evaluates : ExpressionEvaluates program context evidence source
          environment before condition (.bool true) conditionHeap)
        (body_executes : StatementsExecute program context evidence source environment
          conditionHeap body bodyFinalContext (.returned result) after) :
        WhileExecutes program context evidence source environment before condition
          body context (.returned result) after

  /-- Fuel-free execution of the iterative portion of a canonical for loop. -/
  inductive ForLoopExecutes (program : Program) :
      Context → EvidenceEnvironment → TypedSource → Environment →
        Heap → ExpressionId → List ForItemForm → List StatementId →
        Context → ControlOutcome → Heap → Prop where
    | done
        {context evidence source environment before after condition post body}
        (condition_evaluates : ExpressionEvaluates program context evidence source
          environment before condition (.bool false) after) :
        ForLoopExecutes program context evidence source environment before condition
          post body context (.fallthrough environment) after
    | nextFallthrough
        {context evidence source environment before conditionHeap bodyHeap postHeap
          after condition post body bodyFinalContext postFinalContext bodyEnvironment
          postEnvironment outcome}
        (condition_evaluates : ExpressionEvaluates program context evidence source
          environment before condition (.bool true) conditionHeap)
        (body_executes : StatementsExecute program context evidence source environment
          conditionHeap body bodyFinalContext (.fallthrough bodyEnvironment) bodyHeap)
        (post_executes : ForItemsExecute program context evidence source environment
          bodyHeap post postFinalContext postEnvironment postHeap)
        (next : ForLoopExecutes program context evidence source environment postHeap
          condition post body context outcome after) :
        ForLoopExecutes program context evidence source environment before condition
          post body context outcome after
    | nextContinue
        {context evidence source environment before conditionHeap bodyHeap postHeap
          after condition post body bodyFinalContext postFinalContext bodyEnvironment
          postEnvironment outcome}
        (condition_evaluates : ExpressionEvaluates program context evidence source
          environment before condition (.bool true) conditionHeap)
        (body_executes : StatementsExecute program context evidence source environment
          conditionHeap body bodyFinalContext (.continuing bodyEnvironment) bodyHeap)
        (post_executes : ForItemsExecute program context evidence source environment
          bodyHeap post postFinalContext postEnvironment postHeap)
        (next : ForLoopExecutes program context evidence source environment postHeap
          condition post body context outcome after) :
        ForLoopExecutes program context evidence source environment before condition
          post body context outcome after
    | breaks
        {context evidence source environment before conditionHeap after condition post
          body bodyFinalContext bodyEnvironment}
        (condition_evaluates : ExpressionEvaluates program context evidence source
          environment before condition (.bool true) conditionHeap)
        (body_executes : StatementsExecute program context evidence source environment
          conditionHeap body bodyFinalContext (.breaking bodyEnvironment) after) :
        ForLoopExecutes program context evidence source environment before condition
          post body context (.fallthrough environment) after
    | returns
        {context evidence source environment before conditionHeap after condition post
          body bodyFinalContext result}
        (condition_evaluates : ExpressionEvaluates program context evidence source
          environment before condition (.bool true) conditionHeap)
        (body_executes : StatementsExecute program context evidence source environment
          conditionHeap body bodyFinalContext (.returned result) after) :
        ForLoopExecutes program context evidence source environment before condition
          post body context (.returned result) after

end

namespace StatementRoots

theorem length_eq {roots : List NodeId} {statements : List StatementId}
    (extracted : StatementRoots roots statements) :
    roots.length = statements.length := by
  induction extracted with
  | nil => rfl
  | cons _ induction => simp [induction]

end StatementRoots

namespace ExpressionEvaluates

/-- Every successful expression derivation is rooted in an actual occurrence
table member; no lookup function is trusted by the judgment. -/
theorem contains
    {program : Program} {context : Context} {evidence : EvidenceEnvironment}
    {source : TypedSource} {environment : Environment}
    {before after : Heap} {id : ExpressionId} {value : Value}
    (evaluation : ExpressionEvaluates program context evidence source environment
      before id value after) :
    ∃ node, ContainsExpression source id node := by
  cases evaluation with
  | intro contains _ _ => exact ⟨_, contains⟩
  | generalizedLocal contains _ _ _ _ _ _ _ _ => exact ⟨_, contains⟩

end ExpressionEvaluates

namespace StatementExecutes

/-- Every successful statement derivation is likewise occurrence-backed. -/
theorem contains
    {program : Program} {context : Context} {evidence : EvidenceEnvironment}
    {source : TypedSource} {environment : Environment}
    {before after : Heap} {id : StatementId} {finalContext : Context}
    {outcome : ControlOutcome}
    (execution : StatementExecutes program context evidence source environment
      before id finalContext outcome after) :
    ∃ node, ContainsStatement source id node := by
  cases execution <;> first | exact ⟨_, by assumption⟩

end StatementExecutes

namespace CoercionPathExecutes

theorem empty
    {program : Program} {context : Context} {evidence : EvidenceEnvironment}
    {before after : Heap} {input output : Value}
    (execution : CoercionPathExecutes program context evidence before [] input
      output after) :
    output = input ∧ after = before := by
  cases execution
  exact ⟨rfl, rfl⟩

end CoercionPathExecutes

end Solcore.SourceSemantics.Dynamic
