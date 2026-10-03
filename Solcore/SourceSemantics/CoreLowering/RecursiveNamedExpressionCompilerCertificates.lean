import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionInstantiationLaws
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCallSelectionCertificates
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionContextualBuiltins

/-! The actual successful expression pass supplies the existing recursive
call Tree. A local admission filter states the covered source forms and their
compiler child positions. It is not a second expression grammar. Source typing,
ordinary metadata, reached selection coverage and retained domain order remain
static inputs. No expression evaluation or called-body meaning is stored here. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionCompilerCertificates
open Core Frontend SourceInference CompatibleExpressionPrimitives
open CompatibleExpressionConditionals CompatibleExpressionConstructors CompatibleExpressionMembers
open DataPatternValues CallableAncestryPairedLookup RecursiveNamedCatalog
open RecursiveNamedCallSelectionCertificates

abbrev ValuesContext := SourceCoreCompatibleValues.Context
abbrev Scope := SourceCoreLocalCell.Scope

/-- The compiler visits ordinary operands and direct-call arguments in this
order. Synthetic direct callee references are validated separately. -/
def evaluationChildren : ExpressionForm → List ExpressionId
  | .group child | .unary _ child | .member child _ _ => [child]
  | .binary left _ right | .index left right => [left, right]
  | .tuple children | .constructor _ children | .call _ children (.declaration _)
    | .call _ children (.builtinFunction _) => children
  | .conditional condition yes no => [condition, yes, no]
  | _ => []

/-- Nonrecursive form admission. Products with other arities, indirect calls,
lambdas, methods and output coercions are outside this extraction interface. -/
def compositionForm : ExpressionForm → Prop
  | .group _ | .unary _ _ | .binary _ _ _ | .conditional _ _ _
    | .tuple [_, _] | .constructor _ _ | .member _ _ _ | .index _ _
    | .call _ _ (.builtinFunction _) | .call _ _ (.declaration _) => True
  | _ => False

structure Admission (source : TypedSource) (admitted : ExpressionId → Prop) : Prop where
  found : ∀ id, admitted id → ∃ node, source.lookupExpression? id = some node
  shape : ∀ id node, admitted id → source.lookupExpression? id = some node →
    CompatibleExpressionBuiltins.Syntax source id ∨ compositionForm node.form
  children : ∀ id node, admitted id → source.lookupExpression? id = some node →
    ∀ child, child ∈ evaluationChildren node.form → admitted child

variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : Program}
  {headers : Inventory prepared values ambient.definitions program} {compilation : SourceCoreFunctions.Context}

/-- Source signature rows authenticate the raw parameters and result separately
from native packing. These facts cannot be recovered from native type erasure. -/
structure SourceTypes (headers : Inventory prepared values ambient.definitions program)
    (context : SourceSemantics.Context) : Prop where
  parameters : ∀ header, header ∈ headers → ∀ signature,
    signature ∈ context.signatures.functions → header.instantiation.declaration = signature.id →
    signature.parameterTypes.map (TypeSystem.ParameterSubstitution.apply header.instantiation.parameterSubstitution) =
      header.bindings.map (fun binding => binding.1.scheme.body)
  result : ∀ header, header ∈ headers → ∀ signature,
    signature ∈ context.signatures.functions → header.instantiation.declaration = signature.id →
    header.instantiation.parameterSubstitution.apply (TypeSystem.Ty.productMany signature.returnTypes) = header.function.resultType
  projections : ∀ header, header ∈ headers →
    (header.bindings.map (fun binding => binding.1.scheme.body)).mapM values.checked.catalog.project =
      .ok (header.bindings.map Prod.snd)
  evidence : ∀ header, header ∈ headers → header.function.evidence = []

structure PolicyFor (policy : SourceCoreFunctions.Policy) (compilation : SourceCoreFunctions.Context)
    (readFuel : Nat) (values : ValuesContext) (source : TypedSource) (scope : Scope)
    (reasonAt : ExpressionId → Word) (admitted : ExpressionId → Prop) : Prop where
  fragment : CompatibleExpressionBuiltins.PolicyFor policy compilation readFuel values source scope reasonAt
  special : ∀ id, admitted id → ∀ child budget, (match policy.lowerSpecial? with
    | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
    | some lower => lower compilation child budget source scope id reasonAt) = .ok none
  read : ∀ id, admitted id → policy.readExpression source id =
    SourceCoreCompatibleDataExpressions.readExpression values.checked source id

private theorem bind_accepted {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) : ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem ensureType_ok {site : SourceCoreElaboration.ErrorSite} {expected actual : Core.Ty}
    (checked : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  by_cases same : expected = actual
  · exact same
  · simp [SourceCoreBasic.ensureType, same] at checked


private def selectedUnary (operator : Syntax.UnaryOp) (operand : Ty) : UnaryOp :=
  if operator = .bitNot && operand = .integer then .integerNot else SourceCorePrimitive.unaryOperator operator
private def selectedMode (operand : Ty) : Mode := if operand = .integer then .integer else .word

private theorem unary_selected {catalog : SourceCoreCompatibleCatalog.Catalog}
    {operator : Syntax.UnaryOp} {operand result : TypeSystem.Ty} {core : UnaryOp} {type : Ty}
    (profile : UnaryProfile operator operand result core) (projected : catalog.project operand = .ok type) :
    selectedUnary operator type = core := by
  cases profile <;> cases projected <;> rfl
private theorem binary_selected {catalog : SourceCoreCompatibleCatalog.Catalog}
    {operator : Syntax.BinaryOp} {operand result : TypeSystem.Ty} {mode : Mode} {type : Ty}
    (profile : BinaryProfile operator operand result mode) (projected : catalog.project operand = .ok type) :
    selectedMode type = mode := by
  cases profile <;> cases projected <;> rfl

private inductive Compound : ExpressionForm → Prop where
  | unary (operator : Syntax.UnaryOp) (operand : ExpressionId) : Compound (.unary operator operand)
  | binary (operator : Syntax.BinaryOp) (left right : ExpressionId) : Compound (.binary left operator right)
  | group (inner : ExpressionId) : Compound (.group inner)
  | pair (left right : ExpressionId) : Compound (.tuple [left, right])
  | conditional (condition thenId elseId : ExpressionId) : Compound (.conditional condition thenId elseId)

private inductive Step (policy : SourceCoreFunctions.Policy) (body : SourceCoreFunctions.BodyLowerer)
    (fuel : Nat) (context : SourceCoreFunctions.Context) (values : ValuesContext)
    (source : TypedSource) (scope : Scope) (reasonAt : ExpressionId → Word)
    (id : ExpressionId) (node : ExpressionNode) : SourceCoreBasic.LoweredExpr → Prop where
  | unary {operator operand child}
      (form : node.form = .unary operator operand)
      (metadata : Metadata values.checked source id node (selectedUnary operator child.type).resultType)
      (generated : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope operand reasonAt = .ok child)
      (operandType : (selectedUnary operator child.type).operandType = child.type) :
      Step policy body fuel context values source scope reasonAt id node
        ⟨(selectedUnary operator child.type).resultType, LocalPrimitiveResults.unary (selectedUnary operator child.type) child.expression⟩
  | binary {operator left right first second}
      (form : node.form = .binary left operator right)
      (metadata : Metadata values.checked source id node ((selectedMode first.type).resultType operator))
      (firstGenerated : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope left reasonAt = .ok first)
      (secondGenerated : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope right reasonAt = .ok second)
      (leftType : (selectedMode first.type).operandType operator = first.type)
      (rightType : (selectedMode first.type).operandType operator = second.type) :
      Step policy body fuel context values source scope reasonAt id node
        ⟨(selectedMode first.type).resultType operator, (selectedMode first.type).binary operator first.expression second.expression⟩
  | group {inner lowered}
      (form : node.form = .group inner) (metadata : Metadata values.checked source id node lowered.type)
      (generated : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope inner reasonAt = .ok lowered) :
      Step policy body fuel context values source scope reasonAt id node lowered
  | pair {left right first second}
      (form : node.form = .tuple [left, right])
      (metadata : Metadata values.checked source id node (.product first.type second.type))
      (firstGenerated : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope left reasonAt = .ok first)
      (secondGenerated : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope right reasonAt = .ok second) :
      Step policy body fuel context values source scope reasonAt id node
        ⟨.product first.type second.type, LocalSequence.pair first.type second.type first.expression second.expression⟩

  | conditional {condition thenId elseId conditionCode thenCode elseCode type}
      (form : node.form = .conditional condition thenId elseId)
      (metadata : Metadata values.checked source id node type)
      (conditionGenerated : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope condition reasonAt = .ok ⟨.bool, conditionCode⟩)
      (thenGenerated : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope thenId reasonAt = .ok ⟨type, thenCode⟩)
      (elseGenerated : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel context source scope elseId reasonAt = .ok ⟨type, elseCode⟩) :
      Step policy body fuel context values source scope reasonAt id node
        ⟨type, LocalControl.choose type conditionCode thenCode elseCode⟩

private theorem step_of_functions
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {context : SourceCoreFunctions.Context} {values : ValuesContext}
    {source : TypedSource} {scope : Scope} {id : ExpressionId} {node : ExpressionNode}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (found : source.lookupExpression? id = some node) (compound : Compound node.form)
    (special : ∀ child budget, (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower context child budget source scope id reasonAt) = .ok none)
    (readPolicy : policy.readExpression source id = SourceCoreCompatibleDataExpressions.readExpression values.checked source id)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body (fuel + 1) context source scope id reasonAt = .ok lowered) :
    Step policy body fuel context values source scope reasonAt id node lowered := by
  rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  by_cases owner : id.occurrence.owner = source.owner
  · simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte, found,
      bind, Except.bind, pure, Except.pure] at accepted
    have bypass := special (fun budget childSource childScope childId childReasonAt =>
      SourceCoreFunctions.lowerExpressionWithPolicy policy body (min budget fuel) context childSource childScope childId childReasonAt) (fuel + 1)
    cases hook : policy.lowerSpecial? <;> simp only [hook] at accepted bypass
    all_goals try rw [bypass] at accepted
    all_goals
      generalize form : node.form = shape at compound
      cases compound <;> simp only [form, readPolicy, bind, Except.bind, pure, Except.pure] at accepted
    all_goals
      cases read : SourceCoreCompatibleDataExpressions.readExpression values.checked source id with
      | error error => simp [read] at accepted
      | ok pair =>
        obtain ⟨other, type⟩ := pair
        have metadata := CompatibleExpressionReads.metadata_of_read read
        have same := Option.some.inj (metadata.found.symm.trans found)
        subst other
        simp only [read, form] at accepted
        first
        | obtain ⟨child, generated, afterChild⟩ := bind_accepted accepted
          obtain ⟨output, operandChecked, afterOperand⟩ := bind_accepted afterChild
          cases output
          obtain ⟨output, resultChecked, outputEq⟩ := bind_accepted afterOperand
          cases output
          have operandType := ensureType_ok operandChecked
          have resultType := ensureType_ok resultChecked
          subst type
          simp only [pure, Except.pure, Except.ok.injEq] at outputEq
          subst lowered
          exact .unary form metadata generated operandType
        | obtain ⟨first, generated, afterFirst⟩ := bind_accepted accepted
          obtain ⟨second, secondGenerated, afterSecond⟩ := bind_accepted afterFirst
          split at afterSecond <;>
            obtain ⟨output, firstChecked, afterChecked⟩ := bind_accepted afterSecond <;> cases output <;>
            obtain ⟨output, secondChecked, afterSecondChecked⟩ := bind_accepted afterChecked <;> cases output <;>
            obtain ⟨output, resultChecked, outputEq⟩ := bind_accepted afterSecondChecked <;> cases output
          all_goals
            rename_i branch
            have firstType := ensureType_ok firstChecked
            have secondType := ensureType_ok secondChecked
            have resultType := ensureType_ok resultChecked
            subst type
            simp only [pure, Except.pure, Except.ok.injEq] at outputEq
            subst lowered
            simpa only [selectedMode, branch, ↓reduceIte, Mode.binary, Mode.resultType] using (Step.binary form (by simpa only [selectedMode, branch, ↓reduceIte, Mode.resultType] using metadata)
              generated secondGenerated (by simpa only [selectedMode, branch, ↓reduceIte, Mode.operandType] using firstType)
              (by simpa only [selectedMode, branch, ↓reduceIte, Mode.operandType] using secondType))
        | obtain ⟨child, generated, afterChild⟩ := bind_accepted accepted
          obtain ⟨output, checked, outputEq⟩ := bind_accepted afterChild
          cases output
          have same := ensureType_ok checked
          subst type
          simp only [pure, Except.pure, Except.ok.injEq] at outputEq
          subst lowered
          exact .group form metadata generated
        | obtain ⟨first, generated, afterFirst⟩ := bind_accepted accepted
          obtain ⟨second, secondGenerated, afterSecond⟩ := bind_accepted afterFirst
          obtain ⟨output, checked, outputEq⟩ := bind_accepted afterSecond
          cases output
          have same := ensureType_ok checked
          subst type
          simp only [pure, Except.pure, Except.ok.injEq] at outputEq
          subst lowered
          exact .pair form metadata generated secondGenerated
        | obtain ⟨condition, conditionGenerated, afterCondition⟩ := bind_accepted accepted
          obtain ⟨output, conditionChecked, afterChecked⟩ := bind_accepted afterCondition
          cases output
          obtain ⟨thenCode, thenGenerated, afterThen⟩ := bind_accepted afterChecked
          obtain ⟨elseCode, elseGenerated, afterElse⟩ := bind_accepted afterThen
          obtain ⟨output, thenChecked, afterThenChecked⟩ := bind_accepted afterElse
          cases output
          obtain ⟨output, elseChecked, outputEq⟩ := bind_accepted afterThenChecked
          cases output
          have conditionType := ensureType_ok conditionChecked
          have thenType := ensureType_ok thenChecked
          have elseType := ensureType_ok elseChecked
          rcases condition with ⟨conditionType', conditionExpr⟩
          rcases thenCode with ⟨thenType', thenExpr⟩
          rcases elseCode with ⟨elseType', elseExpr⟩
          dsimp only at conditionType thenType elseType
          subst conditionType' thenType' elseType'
          simp only [pure, Except.pure, Except.ok.injEq] at outputEq
          subst lowered
          exact .conditional form metadata conditionGenerated thenGenerated elseGenerated
  · simp [owner, bind, Except.bind] at accepted


theorem tree_projected {readFuel : Nat} {source : TypedSource} {context : SourceSemantics.Context}
    {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word} {scope : Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : Expressions headers compilation readFuel source context solved reasonAt scope id lowered)
    {node : ExpressionNode} (found : source.lookupExpression? id = some node) :
    values.checked.catalog.project node.type = .ok lowered.type := by
  cases tree with
  | fragment child => exact child.projected found
  | node head _ =>
    cases head with
    | primitive primitive =>
      cases primitive with
      | group metadata _ _ _ _ | pair metadata _ _ _ _ _ _ | unary metadata _ _ _ _ _ _
        | binary metadata _ _ _ _ _ _ _ _ _ | conditional metadata _ _ _ _ _ _ _ _ _ _ =>
        have same := Option.some.inj (metadata.found.symm.trans found)
        exact same ▸ metadata.projected
    | constructor receipt _ _ _ =>
      have same := Option.some.inj (receipt.metadata.found.symm.trans found)
      exact same ▸ receipt.metadata.projected
    | member metadata _ _ _ _ =>
      have same := Option.some.inj (metadata.found.symm.trans found)
      exact same ▸ metadata.projected
    | index header _ _ _ _ _ =>
      have same := Option.some.inj (header.metadata.found.symm.trans found)
      exact same ▸ header.metadata.projected
    | builtin builtin =>
      cases builtin with
      | contracted metadata _ _ _ _ =>
        have same := Option.some.inj (metadata.found.symm.trans found)
        exact same ▸ metadata.projected
    | call call =>
      cases call with
      | named _ metadata _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
        have same := Option.some.inj (metadata.found.symm.trans found)
        exact same ▸ metadata.projected

private theorem compiled_children
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel readFuel : Nat}
    {source : TypedSource} {scope : Scope} {reasonAt : ExpressionId → Word} {context : SourceSemantics.Context}
    {ids : List ExpressionId} {types : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    (unique : NodeOccurrencesUnique source) (typed : ExpressionsHaveTypes source context ids types)
    (generated : ids.mapM (fun id => SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope id reasonAt) = .ok codes)
    (extract : ∀ id, id ∈ ids → ∀ node code, source.lookupExpression? id = some node →
      ExpressionHasType source context id node.type →
      SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope id reasonAt = .ok code →
      Expressions headers compilation readFuel source context compilation.solvedRequirements reasonAt scope id code) :
    ids.length = types.length ∧ CompatibleExpressionConstructors.Nodes source ids types codes ∧
      types.mapM values.checked.catalog.project = .ok (codes.map (·.type)) ∧
      ∀ id code, (id, code) ∈ ids.zip codes →
        Expressions headers compilation readFuel source context compilation.solvedRequirements reasonAt scope id code := by
  induction ids generalizing types codes with
  | nil =>
    cases typed
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at generated
    subst codes
    exact ⟨rfl, .nil, rfl, by simp⟩
  | cons id ids ih =>
    cases typed with
    | @cons _ _ _ type types head tail =>
      rw [List.mapM_cons] at generated
      obtain ⟨code, first, generated⟩ := bind_accepted generated
      obtain ⟨restCodes, rest, generated⟩ := bind_accepted generated
      cases generated
      obtain ⟨node, contains, sourceType⟩ := head.stored_type
      have found := lookupExpression?_complete unique contains
      have child := extract id (by simp) node code found (sourceType ▸ head) first
      obtain ⟨count, nodes, projected, children⟩ := ih tail rest (fun id member => extract id (by simp [member]))
      refine ⟨congrArg Nat.succ count, .cons ⟨node, found, sourceType⟩ nodes, ?_, ?_⟩
      · simp [List.mapM_cons, ← sourceType, tree_projected child found, projected, Functor.map, Except.map, bind, Except.bind]
      · intro other otherCode member
        rcases List.mem_cons.mp member with same | remaining
        · cases same; exact child
        · exact children other otherCode remaining

private theorem named_source_types {source : TypedSource} {context : SourceSemantics.Context}
    {id callee : ExpressionId} {arguments : List ExpressionId} {node : ExpressionNode}
    {header : Header prepared values ambient.definitions program}
    (sourceTypes : SourceTypes headers context) (member : header ∈ headers)
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee arguments (.declaration header.instantiation)) (coercions : node.coercions = [])
    (validInstantiation : SourceSemantics.DeclarationInstantiation.Admissible context header.instantiation →
      SourceSemantics.DeclarationInstantiation.Valid context header.instantiation)
    (typed : ExpressionHasType source context id node.type) :
    ExpressionsHaveTypes source context arguments (header.bindings.map (fun binding => binding.1.scheme.body)) ∧
      node.type = header.function.resultType ∧
      ∃ calleeNode name, source.lookupExpression? callee = some calleeNode ∧
        calleeNode.form = .reference name (.declaration header.instantiation) ∧
        calleeNode.requirements = [] ∧ calleeNode.coercions = [] ∧
        SourceSemantics.DeclarationInstantiation.Valid context header.instantiation := by
  generalize typeEq : node.type = type at typed
  cases typed with
  | @intro _ _ actualNode rawType plan contains raw _ _ _ valid =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
    subst actualNode
    have path := valid.outputPath
    rw [coercions] at path
    cases path
    rw [form] at raw
    generalize resultEq : node.type = result at raw
    cases raw with
    | directCall calleeValid application argumentsTyped =>
      cases application with
      | intro signatureMember instantiationValid declarationEq parameterEq resultEq _ _ =>
        have parameters := parameterEq.symm.trans (sourceTypes.parameters header member _ signatureMember declarationEq)
        have result := resultEq.symm.trans (sourceTypes.result header member _ signatureMember declarationEq)
        rw [parameters] at argumentsTyped
        refine ⟨argumentsTyped, result, ?_⟩
        cases calleeValid with
        | @intro calleeNode name _ contains form valid _ requirements coercions =>
          exact ⟨calleeNode, name, lookupExpression?_complete unique contains, form, requirements, coercions,
            validInstantiation valid⟩

private theorem cons_certificates {certificate : GenericExpressionMeaning.Certificate}
    {scope : Scope} {id : ExpressionId} {code : SourceCoreBasic.LoweredExpr}
    {entries : List (ExpressionId × SourceCoreBasic.LoweredExpr)}
    (head : certificate scope id code)
    (tail : ∀ child lowered, (child, lowered) ∈ entries → certificate scope child lowered) :
    ∀ child lowered, (child, lowered) ∈ (id, code) :: entries → certificate scope child lowered := by
  intro child lowered member
  rcases List.mem_cons.mp member with same | rest
  · cases same; exact head
  · exact tail child lowered rest

private theorem child_trees
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel readFuel : Nat}
    {source : TypedSource} {scope : Scope} {reasonAt : ExpressionId → Word} {context : SourceSemantics.Context}
    {ids : List ExpressionId} {types : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    (unique : NodeOccurrencesUnique source) (typed : ExpressionsHaveTypes source context ids types)
    (generated : ListRel (Argument values (fun budget source scope id reasonAt =>
      SourceCoreFunctions.lowerExpressionWithPolicy policy body budget compilation source scope id reasonAt)
      fuel source scope reasonAt) (ids.zip types) codes)
    (extract : ∀ id, id ∈ ids → ∀ node code,
      source.lookupExpression? id = some node → ExpressionHasType source context id node.type →
      SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope id reasonAt = .ok code →
      Expressions headers compilation readFuel source context compilation.solvedRequirements reasonAt scope id code) :
    CompatibleExpressionConstructors.Nodes source ids types codes ∧ ∀ id code, (id, code) ∈ ids.zip codes →
      Expressions headers compilation readFuel source context compilation.solvedRequirements reasonAt scope id code := by
  induction ids generalizing types codes with
  | nil => cases typed; cases generated; exact ⟨.nil, by simp⟩
  | cons id ids ih =>
    cases typed with
    | @cons _ _ _ type types head tail =>
      cases generated with
      | @cons _ _ code codes first rest =>
        obtain ⟨node, contains, sourceType⟩ := head.stored_type
        have found := lookupExpression?_complete unique contains
        have child := extract id (by simp) node code found (sourceType ▸ head) first.generated
        obtain ⟨nodes, children⟩ := ih tail rest (fun id member => extract id (by simp [member]))
        refine ⟨.cons ⟨node, found, sourceType⟩ nodes, ?_⟩
        intro other otherCode member
        rcases List.mem_cons.mp member with same | remaining
        · cases same; exact child
        · exact children other otherCode remaining

private theorem builtin_source_types {source : TypedSource} {context : SourceSemantics.Context}
    {id callee : ExpressionId} {arguments : List ExpressionId} {function : BuiltinFunctionId} {node : ExpressionNode}
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee arguments (.builtinFunction function)) (coercions : node.coercions = [])
    (typed : ExpressionHasType source context id node.type) :
    ExpressionsHaveTypes source context arguments function.parameterTypes ∧ node.type = function.returnType := by
  generalize typeEq : node.type = type at typed
  cases typed with
  | @intro _ _ actualNode rawType plan contains raw _ _ _ valid =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
    subst actualNode
    have path := valid.outputPath
    rw [coercions] at path
    cases path
    rw [form] at raw
    generalize resultEq : node.type = result at raw
    cases raw with
    | builtinCall _ argumentsTyped => exact ⟨argumentsTyped, rfl⟩

/-- Declaration validity is consumed only at an actually selected call site.
The full reached header and source instantiation are kept, together with the
original source admissibility and its independently well-formed binders. -/
def SelectedDeclarationLaw (headers : Inventory prepared values ambient.definitions program)
    (compilation : SourceCoreFunctions.Context) (source : TypedSource)
    (context : SourceSemantics.Context) (admitted : ExpressionId → Prop) : Prop :=
  ∀ id node callee arguments instantiation (header : Header prepared values ambient.definitions program)
    (policy : SourceCoreFunctions.Policy) index signature,
    admitted id → source.lookupExpression? id = some node →
    node.form = .call callee arguments (.declaration instantiation) →
    SourceCoreFunctions.selectedSignature policy compilation source node instantiation false = .ok (index, signature) →
    header ∈ headers → instantiation = header.instantiation →
    header.slot = index → header.named.signature = signature →
    TypeParameterBindersWellFormed context →
    SourceSemantics.DeclarationInstantiation.Admissible context instantiation →
    SourceSemantics.DeclarationInstantiation.Valid context instantiation

/-- A former law for all admitted calls can be restricted to the selected site.
The reverse implication is neither required nor asserted. -/
theorem SelectedDeclarationLaw.of_declaration
    {source : TypedSource} {context : SourceSemantics.Context} {admitted : ExpressionId → Prop}
    (law : CompatibleExpressionInstantiationLaws.DeclarationLaw source context admitted) :
    SelectedDeclarationLaw headers compilation source context admitted := by
  intro id node callee arguments instantiation _header _policy _index _signature
    allowed found form _selected _member _same _slot _signatureEq _binders admissible
  exact law id node callee arguments instantiation allowed found form admissible

/-- The existing Tree is extracted by the actual compiler's fuel induction.
Each child keeps its original compiler result and source type. -/
theorem tree_of_functions_at
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {readFuel : Nat} {source : TypedSource} {scope : Scope} {reasonAt : ExpressionId → Word}
    {context : SourceSemantics.Context} {admitted : ExpressionId → Prop}
    (admission : Admission source admitted) (coverage : ReachedCoverage headers compilation source admitted)
    (sourceTypes : SourceTypes headers context)
    (order : ∀ id callee arguments instantiation node, admitted id → source.lookupExpression? id = some node →
      node.form = .call callee arguments (.declaration instantiation) → Ordered compilation.plan instantiation)
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (signatures : context.signatures = values.checked.signatures)
    (constructorValid : CompatibleExpressionInstantiationLaws.ConstructorLaw source context admitted)
    (fragmentValid : CompatibleExpressionInstantiationLaws.ConstructorLaw source context (CompatibleExpressionBuiltins.Syntax source))
    (selectedValid : SelectedDeclarationLaw headers compilation source context admitted)
    (policyFor : PolicyFor policy compilation readFuel values source scope reasonAt admitted)
    (native : SourceCoreGeneralFunctions.CallableContext) (active : TypeSystem.Substitution)
    (profile : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some native) active)
    (fragmentCoercions : ∀ id node, CompatibleExpressionBuiltins.Syntax source id → source.lookupExpression? id = some node → node.coercions = [])
    (coercions : ∀ id node, admitted id → source.lookupExpression? id = some node → node.coercions = [])
    {fuel : Nat} {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (allowed : admitted id) (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source context id node.type)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope id reasonAt = .ok lowered) :
    Expressions headers compilation readFuel source context compilation.solvedRequirements reasonAt scope id lowered := by
  induction fuel generalizing id node lowered with
  | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  | succ fuel ih =>
    rcases admission.shape id node allowed found with fragment | composition
    · exact .fragment (CompatibleExpressionBuiltins.tree_of_functions_with_validity unique declarations signatures fragmentValid
        policyFor.fragment native active profile fragmentCoercions fragment found typed accepted)
    have owner : id.occurrence.owner = source.owner := by
      by_cases same : id.occurrence.owner = source.owner
      · exact same
      · rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
        simp [same, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at accepted
    have children := admission.children id node allowed found
    have special := policyFor.special id allowed
    have readPolicy := policyFor.read id allowed
    cases form : node.form with
    | group inner =>
      have step := step_of_functions found (by rw [form]; constructor) special readPolicy accepted
      cases step with
      | @group actualInner actualLowered otherForm metadata generated =>
        have same := ExpressionForm.group.inj (form.symm.trans otherForm)
        subst inner
        obtain ⟨innerNode, innerFound, sourceType, childTyped⟩ :=
          CompatibleExpressionProducts.group_source_types unique found form metadata.coercions typed
        have childTree := ih (children actualInner (by simp [evaluationChildren, form])) innerFound childTyped generated
        exact .node (entries := [(actualInner, lowered)]) (.primitive (.group metadata form innerFound sourceType ⟨rfl, by simp⟩))
          (cons_certificates childTree (by simp))
      | unary otherForm _ _ _ | binary otherForm _ _ _ _ _ | pair otherForm _ _ _ | conditional otherForm _ _ _ _ => simp [form] at otherForm
    | unary operator operand =>
      have step := step_of_functions found (by rw [form]; constructor) special readPolicy accepted
      cases step with
      | @unary actualOperator actualOperand compiled otherForm metadata generated inputChecked =>
        obtain ⟨rfl, rfl⟩ := ExpressionForm.unary.inj (form.symm.trans otherForm)
        obtain ⟨childNode, core, childFound, childTyped, sourceProfile⟩ :=
          unary_source_types unique found form metadata.coercions metadata.requirements typed
        have childTree := ih (children operand (by simp [evaluationChildren, form])) childFound childTyped generated
        have chosen := unary_selected sourceProfile (tree_projected childTree childFound)
        rw [chosen] at metadata inputChecked ⊢
        obtain ⟨childType, childCode⟩ := compiled
        dsimp only at inputChecked childTree ⊢
        subst childType
        exact .node (entries := [(operand, ⟨core.operandType, childCode⟩)]) (.primitive (.unary metadata form childFound rfl rfl sourceProfile ⟨rfl, by simp⟩))
          (cons_certificates childTree (by simp))
      | binary otherForm _ _ _ _ _ | group otherForm _ _ | pair otherForm _ _ _ | conditional otherForm _ _ _ _ => simp [form] at otherForm
    | binary left operator right =>
      have step := step_of_functions found (by rw [form]; constructor) special readPolicy accepted
      cases step with
      | @binary actualOperator actualLeft actualRight first second otherForm metadata firstGenerated secondGenerated leftChecked rightChecked =>
        obtain ⟨rfl, rfl, rfl⟩ := ExpressionForm.binary.inj (form.symm.trans otherForm)
        obtain ⟨leftNode, rightNode, mode, leftFound, rightFound, sameType, leftTyped, rightTyped, sourceProfile⟩ :=
          binary_source_types unique found form metadata.coercions metadata.requirements typed
        have firstTree := ih (children left (by simp [evaluationChildren, form])) leftFound leftTyped firstGenerated
        have secondTree := ih (children right (by simp [evaluationChildren, form])) rightFound rightTyped secondGenerated
        have chosen := binary_selected sourceProfile (tree_projected firstTree leftFound)
        rw [chosen] at metadata leftChecked rightChecked ⊢
        obtain ⟨firstType, leftCode⟩ := first
        obtain ⟨secondType, rightCode⟩ := second
        dsimp only at leftChecked rightChecked firstTree secondTree ⊢
        subst firstType secondType
        exact .node (entries := [(left, ⟨mode.operandType operator, leftCode⟩), (right, ⟨mode.operandType operator, rightCode⟩)]) (.primitive (.binary metadata form leftFound rightFound rfl sameType.symm rfl sourceProfile
          ⟨rfl, by simp⟩ ⟨rfl, by simp⟩)) (cons_certificates firstTree (cons_certificates secondTree (by simp)))
      | unary otherForm _ _ _ | group otherForm _ _ | pair otherForm _ _ _ | conditional otherForm _ _ _ _ => simp [form] at otherForm
    | tuple items =>
      cases items with
      | nil => simp [compositionForm, form] at composition
      | cons left rest =>
        cases rest with
        | nil => simp [compositionForm, form] at composition
        | cons right rest =>
          cases rest with
          | cons => simp [compositionForm, form] at composition
          | nil =>
            have step := step_of_functions found (by rw [form]; constructor) special readPolicy accepted
            cases step with
            | pair otherForm metadata firstGenerated secondGenerated =>
              have same := ExpressionForm.tuple.inj (form.symm.trans otherForm)
              simp only [List.cons.injEq, and_true] at same
              obtain ⟨rfl, rfl⟩ := same
              obtain ⟨leftNode, rightNode, leftFound, rightFound, sourceType, leftTyped, rightTyped⟩ :=
                CompatibleExpressionProducts.pair_source_types unique found form metadata.coercions typed
              have firstTree := ih (children left (by simp [evaluationChildren, form])) leftFound leftTyped firstGenerated
              have secondTree := ih (children right (by simp [evaluationChildren, form])) rightFound rightTyped secondGenerated
              exact .node (entries := [(left, _), (right, _)]) (.primitive (.pair metadata form leftFound rightFound sourceType ⟨rfl, by simp⟩ ⟨rfl, by simp⟩))
                (cons_certificates firstTree (cons_certificates secondTree (by simp)))
            | unary otherForm _ _ _ | binary otherForm _ _ _ _ _ | group otherForm _ _ | conditional otherForm _ _ _ _ => simp [form] at otherForm
    | conditional condition thenId elseId =>
      have step := step_of_functions found (by rw [form]; constructor) special readPolicy accepted
      cases step with
      | @conditional actualCondition actualThen actualElse conditionCode thenCode elseCode type otherForm metadata conditionGenerated thenGenerated elseGenerated =>
        obtain ⟨rfl, rfl, rfl⟩ := ExpressionForm.conditional.inj (form.symm.trans otherForm)
        obtain ⟨conditionNode, thenNode, elseNode, conditionFound, thenFound, elseFound, conditionType, thenType, elseType,
          conditionTyped, thenTyped, elseTyped⟩ := conditional_source_types unique found form metadata.coercions typed
        have conditionTree := ih (children condition (by simp [evaluationChildren, form])) conditionFound conditionTyped conditionGenerated
        have thenTree := ih (children thenId (by simp [evaluationChildren, form])) thenFound thenTyped thenGenerated
        have elseTree := ih (children elseId (by simp [evaluationChildren, form])) elseFound elseTyped elseGenerated
        exact .node (entries := [(condition, ⟨.bool, conditionCode⟩), (thenId, ⟨type, thenCode⟩), (elseId, ⟨type, elseCode⟩)]) (.primitive (.conditional metadata form conditionFound thenFound elseFound conditionType thenType elseType
          ⟨rfl, by simp⟩ ⟨rfl, by simp⟩ ⟨rfl, by simp⟩))
          (cons_certificates conditionTree (cons_certificates thenTree (cons_certificates elseTree (by simp))))
      | unary otherForm _ _ _ | binary otherForm _ _ _ _ _ | group otherForm _ _ | pair otherForm _ _ _ => simp [form] at otherForm
    | constructor instantiation ids =>
      obtain ⟨tag, header, codes, rfl, receipt, count, arguments⟩ := constructor_of_functions found form special readPolicy policyFor.fragment.leaf accepted
      obtain ⟨admissible, argumentsTyped, sourceType⟩ := constructor_source_types unique found form receipt.metadata.coercions typed
      obtain ⟨nodes, childTrees⟩ := child_trees unique argumentsTyped arguments
        (fun child member node code childFound childTyped generated =>
          ih (children child (by simpa [evaluationChildren, form] using member)) childFound childTyped generated)
      have sequence := sequence_of_nodes (certificate := CompatibleExpressionCalls.Entries scope (ids.zip codes)) count nodes
        (fun child code member => ⟨rfl, member⟩)
      exact .node (entries := ids.zip codes) (.constructor receipt form (constructorValid id node instantiation ids allowed found form admissible) sequence) childTrees
    | member base name index =>
      obtain ⟨baseType, baseTyped, projection⟩ := member_source_types unique found form (coercions id node allowed found) typed
      obtain ⟨baseNode, contains, sourceType⟩ := baseTyped.stored_type
      have baseFound := lookupExpression?_complete unique contains
      rw [← sourceType] at baseTyped projection
      obtain ⟨identity, branches, result, code, rfl, metadata, baseMetadata, layout, generated⟩ :=
        member_of_functions signatures found baseFound form projection special readPolicy policyFor.fragment.leaf accepted
      have childTree := ih (children base (by simp [evaluationChildren, form])) baseFound baseTyped generated
      exact .node (entries := [(base, code)]) (.member metadata baseMetadata form layout ⟨rfl, by simp⟩) (cons_certificates childTree (by simp))
    | index base key =>
      obtain ⟨keyType, baseTyped, keyTyped⟩ := CompatibleExpressionIndices.index_source_types unique found form
        (coercions id node allowed found) typed
      obtain ⟨baseNode, baseContains, baseType⟩ := baseTyped.stored_type
      obtain ⟨keyNode, keyContains, actualKeyType⟩ := keyTyped.stored_type
      have baseFound := lookupExpression?_complete unique baseContains
      have keyFound := lookupExpression?_complete unique keyContains
      rw [← actualKeyType] at keyTyped baseType baseTyped
      rw [← baseType] at baseTyped
      obtain ⟨layout, comparison, first, second, rfl, header, firstGenerated, secondGenerated⟩ :=
        CompatibleExpressionIndices.index_of_functions found baseFound form special readPolicy policyFor.fragment.leaf accepted
      have firstTree := ih (children base (by simp [evaluationChildren, form])) baseFound baseTyped firstGenerated
      have secondTree := ih (children key (by simp [evaluationChildren, form])) keyFound keyTyped secondGenerated
      exact .node (entries := [(base, first), (key, second)]) (.index header keyFound form baseType ⟨rfl, by simp⟩ ⟨rfl, by simp⟩)
        (cons_certificates firstTree (cons_certificates secondTree (by simp)))
    | call callee arguments resolution =>
      cases resolution with
      | indirect => simp [compositionForm, form] at composition
      | declaration instantiation =>
        have bypass := special (fun budget childSource childScope childId childReasonAt =>
          SourceCoreFunctions.lowerExpressionWithPolicy policy body (min budget fuel) compilation childSource childScope childId childReasonAt) (fuel + 1)
        cases read : policy.readExpression source id with
        | error error =>
          cases hook : policy.lowerSpecial? <;> simp only [hook] at bypass
          all_goals simp [SourceCoreFunctions.lowerExpressionWithPolicy, owner, found, form, hook, bypass, read,
            bind, Except.bind, pure, Except.pure] at accepted
        | ok pair =>
          obtain ⟨actualNode, nativeType⟩ := pair
          have compatibleRead := read
          rw [readPolicy] at compatibleRead
          have metadata := CompatibleExpressionReads.metadata_of_read compatibleRead
          have same := Option.some.inj (metadata.found.symm.trans found)
          subst actualNode
          obtain ⟨index, signature, specialized, codes, selected, exactRecord, _, argumentsAccepted, _, resultType, emitted, nativeTypeEq⟩ :=
            NamedCalls.Arguments.call_of_accepted metadata.owner found read form bypass accepted
          obtain ⟨header, member, slot, signatureEq, instantiationEq, headerRecord⟩ :=
            RecursiveNamedCallSelectionCertificates.selected_at coverage allowed found form (order id callee arguments instantiation node allowed found form) selected
          subst instantiation
          obtain ⟨argumentsTyped, sourceType, calleeNode, name, calleeFound, calleeForm, calleeRequirements, calleeCoercions, valid⟩ :=
            named_source_types sourceTypes member unique found form metadata.coercions (selectedValid id node callee arguments header.instantiation header policy index signature
              allowed found form selected member rfl slot signatureEq typed.type_admissible.binders) typed
          obtain ⟨count, nodes, projected, childTrees⟩ := compiled_children unique argumentsTyped argumentsAccepted
            (fun child member node code childFound childTyped generated =>
              ih (children child (by simpa [evaluationChildren, form] using member)) childFound childTyped generated)
          have nativeTypes := Except.ok.inj (projected.symm.trans (sourceTypes.projections header member))
          rw [← signatureEq, header.resultType] at resultType
          cases resultType
          have loweredType : lowered.type = header.output := nativeTypeEq
          obtain ⟨loweredType', expression⟩ := lowered
          dsimp only at loweredType
          subst loweredType'
          have sequence := sequence_of_nodes (certificate := CompatibleExpressionCalls.Entries scope (arguments.zip codes)) count nodes
            (fun child code member => ⟨rfl, member⟩)
          have arity : header.function.parameters.length = arguments.length := by rw [header.parameters]; simp only [List.length_map] at count ⊢; omega
          have predicates : header.instantiation.predicates = [] := by
            have matched := CallableNamedMetadata.matches_of_exact (NamedCalls.selected_signature_target selected).1 headerRecord
            exact matched.predicates.symm.trans header.closed
          let emission : NamedCalls.Arguments.Emission compilation source scope id callee arguments header.instantiation
              header.named.signature codes ⟨header.output, expression⟩ :=
            ⟨policy, body, fuel, reasonAt, node, header.output, metadata.owner, found, read, form, bypass, accepted,
              index, signatureEq.symm ▸ selected, argumentsAccepted⟩
          exact .node (entries := arguments.zip codes) (.call (.named member metadata sourceType form calleeFound calleeForm calleeRequirements calleeCoercions
            valid predicates (sourceTypes.evidence header member) arity emission (by change index = header.slot; exact slot.symm) sequence nativeTypes)) childTrees
      | builtinFunction function =>
        have bypass := special (fun budget childSource childScope childId childReasonAt =>
          SourceCoreFunctions.lowerExpressionWithPolicy policy body (min budget fuel) compilation childSource childScope childId childReasonAt) (fuel + 1)
        by_cases owner : id.occurrence.owner = source.owner
        · cases read : policy.readExpression source id with
          | error error =>
            cases hook : policy.lowerSpecial? <;> simp only [hook] at bypass
            all_goals simp [SourceCoreFunctions.lowerExpressionWithPolicy, owner, found, form, hook, bypass, read,
              bind, Except.bind, pure, Except.pure] at accepted
          | ok pair =>
            obtain ⟨actualNode, nativeType⟩ := pair
            have compatibleRead := read
            rw [readPolicy] at compatibleRead
            have metadata := CompatibleExpressionReads.metadata_of_read compatibleRead
            have same := Option.some.inj (metadata.found.symm.trans found)
            subst actualNode
            obtain ⟨calleeNode, calleeType, calleeCode, codes, expression, _, _, reference,
              argumentsAccepted, _, resultType, emitted, rfl⟩ := BuiltinCalls.call_of_accepted owner found read form bypass accepted
            have sourceTypes := builtin_source_types unique found form metadata.coercions typed
            obtain ⟨count, nodes, projected, childTrees⟩ := compiled_children unique sourceTypes.1 argumentsAccepted
              (fun child member node code childFound childTyped generated =>
                ih (children child (by simpa [evaluationChildren, form] using member)) childFound childTyped generated)
            cases reference with
            | @intro index identity calleeExpression _ _ _ _ decorated =>
              cases selected : SourceCoreCallableContracts.descriptor native.table (.builtin function) with
              | error error => simp [profile, SourceCoreGeneralFunctions.callablePolicy, selected, Except.mapError, bind, Except.bind] at decorated
              | ok descriptor =>
                rw [profile, ActualCallablePolicy.builtin_decoration native active compilation source calleeNode function
                  (SourceCoreInteger.builtinParameter function) (SourceCoreInteger.builtinResult function) _ descriptor] at decorated
                cases decorated
                rw [profile, BuiltinCalls.Typed.builtin_call native active compilation source node callee arguments function nativeType _ _ descriptor form] at emitted
                cases emitted
                subst nativeType
                rw [CompatibleBuiltinMeaning.argumentTypes_project function] at projected
                have sequence := sequence_of_nodes (certificate := CompatibleExpressionCalls.Entries scope (arguments.zip codes)) count nodes
                  (fun child code member => ⟨rfl, member⟩)
                exact .node (entries := arguments.zip codes) (.builtin (.contracted metadata form sourceTypes.2 sequence (Except.ok.inj projected).symm)) childTrees
        · rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
          simp only [owner, ne_eq, not_false_eq_true, ↓reduceIte] at accepted
          cases accepted
    | literal | integerLiteral | reference | lambda | proxy => simp [compositionForm, form] at composition

/-- Preserve the former whole-inventory interface as a restriction. -/
theorem tree_of_functions_with_selected_validity
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {readFuel : Nat} {source : TypedSource} {scope : Scope} {reasonAt : ExpressionId → Word}
    {context : SourceSemantics.Context} {admitted : ExpressionId → Prop}
    (admission : Admission source admitted) (coverage : Coverage headers compilation)
    (sourceTypes : SourceTypes headers context)
    (order : ∀ id callee arguments instantiation node, admitted id → source.lookupExpression? id = some node →
      node.form = .call callee arguments (.declaration instantiation) → Ordered compilation.plan instantiation)
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (signatures : context.signatures = values.checked.signatures)
    (constructorValid : CompatibleExpressionInstantiationLaws.ConstructorLaw source context admitted)
    (fragmentValid : CompatibleExpressionInstantiationLaws.ConstructorLaw source context (CompatibleExpressionBuiltins.Syntax source))
    (selectedValid : SelectedDeclarationLaw headers compilation source context admitted)
    (policyFor : PolicyFor policy compilation readFuel values source scope reasonAt admitted)
    (native : SourceCoreGeneralFunctions.CallableContext) (active : TypeSystem.Substitution)
    (profile : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some native) active)
    (fragmentCoercions : ∀ id node, CompatibleExpressionBuiltins.Syntax source id → source.lookupExpression? id = some node → node.coercions = [])
    (coercions : ∀ id node, admitted id → source.lookupExpression? id = some node → node.coercions = [])
    {fuel : Nat} {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (allowed : admitted id) (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source context id node.type)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope id reasonAt = .ok lowered) :
    Expressions headers compilation readFuel source context compilation.solvedRequirements reasonAt scope id lowered := by
  exact tree_of_functions_at admission coverage.restrict sourceTypes order unique declarations signatures
    constructorValid fragmentValid selectedValid policyFor native active profile fragmentCoercions coercions allowed found typed accepted

/-- Preserve the original all-admitted-site interface as a restriction adapter. -/
theorem tree_of_functions_with_validity
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {readFuel : Nat} {source : TypedSource} {scope : Scope} {reasonAt : ExpressionId → Word}
    {context : SourceSemantics.Context} {admitted : ExpressionId → Prop}
    (admission : Admission source admitted) (coverage : Coverage headers compilation)
    (sourceTypes : SourceTypes headers context)
    (order : ∀ id callee arguments instantiation node, admitted id → source.lookupExpression? id = some node →
      node.form = .call callee arguments (.declaration instantiation) → Ordered compilation.plan instantiation)
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (signatures : context.signatures = values.checked.signatures)
    (constructorValid : CompatibleExpressionInstantiationLaws.ConstructorLaw source context admitted)
    (fragmentValid : CompatibleExpressionInstantiationLaws.ConstructorLaw source context (CompatibleExpressionBuiltins.Syntax source))
    (declarationValid : CompatibleExpressionInstantiationLaws.DeclarationLaw source context admitted)
    (policyFor : PolicyFor policy compilation readFuel values source scope reasonAt admitted)
    (native : SourceCoreGeneralFunctions.CallableContext) (active : TypeSystem.Substitution)
    (profile : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some native) active)
    (fragmentCoercions : ∀ id node, CompatibleExpressionBuiltins.Syntax source id → source.lookupExpression? id = some node → node.coercions = [])
    (coercions : ∀ id node, admitted id → source.lookupExpression? id = some node → node.coercions = [])
    {fuel : Nat} {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (allowed : admitted id) (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source context id node.type)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope id reasonAt = .ok lowered) :
    Expressions headers compilation readFuel source context compilation.solvedRequirements reasonAt scope id lowered := by
  exact tree_of_functions_with_selected_validity (policy := policy) (body := body) (readFuel := readFuel)
    (source := source) (scope := scope) (reasonAt := reasonAt) (context := context) (admitted := admitted)
    (admission := admission) (coverage := coverage) (sourceTypes := sourceTypes) (order := order) (unique := unique)
    (declarations := declarations) (signatures := signatures) (constructorValid := constructorValid)
    (fragmentValid := fragmentValid) (selectedValid := SelectedDeclarationLaw.of_declaration declarationValid)
    (policyFor := policyFor) (native := native) (active := active) (profile := profile)
    (fragmentCoercions := fragmentCoercions) (coercions := coercions) (fuel := fuel) (id := id) (node := node)
    (lowered := lowered) (allowed := allowed) (found := found) (typed := typed) (accepted := accepted)

/-- Compatibility with the former false residual scope. -/
theorem tree_of_functions
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {readFuel : Nat} {source : TypedSource} {scope : Scope} {reasonAt : ExpressionId → Word}
    {context : SourceSemantics.Context} {admitted : ExpressionId → Prop}
    (admission : Admission source admitted) (coverage : Coverage headers compilation)
    (sourceTypes : SourceTypes headers context)
    (order : ∀ id callee arguments instantiation node, admitted id → source.lookupExpression? id = some node →
      node.form = .call callee arguments (.declaration instantiation) → Ordered compilation.plan instantiation)
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (signatures : context.signatures = values.checked.signatures)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = false)
    (policyFor : PolicyFor policy compilation readFuel values source scope reasonAt admitted)
    (native : SourceCoreGeneralFunctions.CallableContext) (active : TypeSystem.Substitution)
    (profile : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some native) active)
    (fragmentCoercions : ∀ id node, CompatibleExpressionBuiltins.Syntax source id → source.lookupExpression? id = some node → node.coercions = [])
    (coercions : ∀ id node, admitted id → source.lookupExpression? id = some node → node.coercions = [])
    {fuel : Nat} {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (allowed : admitted id) (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source context id node.type)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope id reasonAt = .ok lowered) :
    Expressions headers compilation readFuel source context compilation.solvedRequirements reasonAt scope id lowered := by
  exact tree_of_functions_with_validity (policy := policy) (body := body) (readFuel := readFuel) (source := source)
    (scope := scope) (reasonAt := reasonAt) (context := context) (admitted := admitted) (admission := admission)
    (coverage := coverage) (sourceTypes := sourceTypes) (order := order) (unique := unique)
    (declarations := declarations) (signatures := signatures)
    (constructorValid := CompatibleExpressionInstantiationLaws.ConstructorLaw.of_closed closed residual)
    (fragmentValid := CompatibleExpressionInstantiationLaws.ConstructorLaw.of_closed closed residual)
    (declarationValid := CompatibleExpressionInstantiationLaws.DeclarationLaw.of_closed closed residual)
    (policyFor := policyFor) (native := native) (active := active) (profile := profile)
    (fragmentCoercions := fragmentCoercions) (coercions := coercions) (fuel := fuel) (id := id) (node := node)
    (lowered := lowered) (allowed := allowed) (found := found) (typed := typed) (accepted := accepted)

private theorem ordinary_general {source : TypedSource} {locals : SourceCoreLocalPolymorphism.Catalog}
    {owner : SourceSpecialization.SpecializationKey} (ordinary : CompatibleExpressionBuiltins.Ordinary source locals owner) :
    CompatibleExpressionGeneral.Ordinary source locals owner :=
  ⟨fun id node child => ordinary.requirements id node (.fragment child),
   fun id node child => ordinary.coercions id node (.fragment child),
   fun id child => ordinary.notInitializer id (.fragment child),
   fun id node name binder child => ordinary.localBinder id node name binder (.fragment child)⟩

private theorem contextualSource_fragment
    (program : CheckedProgram) (plan : SourceSpecializationWorklist.Plan)
    (locals : SourceCoreLocalPolymorphism.Catalog) (owner : SourceSpecialization.SpecializationKey)
    (parent : Option SourceCoreLocalEvidence.Prepared) {source : TypedSource} {id : ExpressionId}
    (ordinary : CompatibleExpressionBuiltins.Ordinary source locals owner) (syntaxTree : CompatibleExpressionBuiltins.Syntax source id) :
    SourceCoreGeneralFunctions.contextualSource program plan locals owner parent source id = .ok source := by
  cases syntaxTree with
  | fragment child => exact CompatibleExpressionGeneral.contextualSource_fragment program plan locals owner parent (ordinary_general ordinary) child
  | proxy found form | unary found form _ | binary found form _ _ | group found form _ | pair found form _ _ | conditional found form _ _ _ | constructor found form _ | member found form _ | index found form _ _ _ | builtin found form _ =>
      simp [SourceCoreGeneralFunctions.contextualSource, found, form, bind, Except.bind, pure, Except.pure]

private theorem evidence_fragment (program : CheckedProgram) (projector : SourceCoreEvidence.Projector)
    (caller : SourceSpecialization.SpecializedFunction) (context : SourceCoreFunctions.Context)
    (child : SourceCoreFunctions.ExpressionLowerer) (fuel : Nat) (scope : Scope)
    (reasonAt : ExpressionId → Word) (callables : SourceCoreFunctions.CallablePolicy)
    {source : TypedSource} {id : ExpressionId} {node : ExpressionNode}
    (syntaxTree : CompatibleExpressionBuiltins.Syntax source id) (found : source.lookupExpression? id = some node)
    (requirements : node.requirements = CompatibleExpressionLiterals.owned node.form) (coercions : node.coercions = []) :
    SourceCoreEvidence.lowerWithProjector program projector caller context child fuel source scope id reasonAt callables = .ok none := by
  have ordinaryOwned : SourceCompilationPlan.ordinaryOwnedRequirements? node = some (CompatibleExpressionLiterals.owned node.form) := by
    unfold SourceCompilationPlan.ordinaryOwnedRequirements?
    rw [requirements, coercions]
    change (if (CompatibleExpressionLiterals.owned node.form).length < 0 then none else
      if CompatibleExpressionLiterals.owned node.form = (CompatibleExpressionLiterals.owned node.form).take
          ((CompatibleExpressionLiterals.owned node.form).length - 0) ++ [] then
        some ((CompatibleExpressionLiterals.owned node.form).take ((CompatibleExpressionLiterals.owned node.form).length - 0)) else none) = _
    simp
  cases syntaxTree with
  | fragment old => exact CompatibleExpressionGeneral.evidence_fragment program projector caller context child fuel scope reasonAt callables old found requirements coercions
  | proxy originalFound form | unary originalFound form _ | binary originalFound form _ _ | group originalFound form _ | pair originalFound form _ _ | conditional originalFound form _ _ _ | constructor originalFound form _ | member originalFound form _ | index originalFound form _ _ _ | builtin originalFound form _ =>
      have same := Option.some.inj (originalFound.symm.trans found)
      subst node
      simp [SourceCoreEvidence.lowerWithProjector, found, form, ordinaryOwned, requirements, coercions,
        CompatibleExpressionLiterals.owned, bind, Except.bind, pure, Except.pure]

private theorem fragment_has_node {source : TypedSource} {id : ExpressionId} (syntaxTree : CompatibleExpressionBuiltins.Syntax source id) :
    ∃ node, source.lookupExpression? id = some node := by
  cases syntaxTree with
  | fragment child => exact CompatibleExpressionGeneral.fragment_has_node child
  | proxy found _ | unary found _ _ | binary found _ _ _ | group found _ _ | pair found _ _ _ | conditional found _ _ _ _ | constructor found _ _ | member found _ _ | index found _ _ _ _ | builtin found _ _ => exact ⟨_, found⟩


/-- Ordinary metadata for the admitted occurrences and the existing builtin
fragment. The selected caller is separately required to have no assumptions;
this keeps direct named calls on the actual ordinary lowering branch. -/
structure Ordinary (source : TypedSource) (locals : SourceCoreLocalPolymorphism.Catalog)
    (owner : SourceSpecialization.SpecializationKey) (admitted : ExpressionId → Prop) : Prop where
  fragment : CompatibleExpressionBuiltins.Ordinary source locals owner
  requirements : ∀ id node, admitted id → source.lookupExpression? id = some node →
    node.requirements = CompatibleExpressionLiterals.owned node.form
  coercions : ∀ id node, admitted id → source.lookupExpression? id = some node → node.coercions = []
  notInitializer : ∀ id, admitted id → locals.bindings.find?
    (fun binding => decide (binding.caller = owner ∧ binding.initializer = id)) = none
  localBinder : ∀ id node name binder, admitted id → source.lookupExpression? id = some node →
    node.form = .reference name (.local binder) →
    locals.bindings.any (fun binding => decide (binding.caller = owner ∧ binding.binder.id = binder)) = false

private theorem contextualSource_admitted
    (checkedProgram : CheckedProgram) (plan : SourceSpecializationWorklist.Plan)
    (locals : SourceCoreLocalPolymorphism.Catalog) (owner : SourceSpecialization.SpecializationKey)
    {source : TypedSource} {id : ExpressionId} {node : ExpressionNode} {admitted : ExpressionId → Prop}
    (admission : Admission source admitted) (ordinary : Ordinary source locals owner admitted)
    (allowed : admitted id) (found : source.lookupExpression? id = some node) :
    SourceCoreGeneralFunctions.contextualSource checkedProgram plan locals owner none source id = .ok source := by
  rcases admission.shape id node allowed found with fragment | composition
  · exact contextualSource_fragment checkedProgram plan locals owner none ordinary.fragment fragment
  · cases form : node.form <;> simp [compositionForm, form] at composition
    all_goals simp [SourceCoreGeneralFunctions.contextualSource, found, form, bind, Except.bind, pure, Except.pure]

private theorem evidence_admitted
    (checkedProgram : CheckedProgram) (projector : SourceCoreEvidence.Projector)
    (caller : SourceSpecialization.SpecializedFunction) (context : SourceCoreFunctions.Context)
    (child : SourceCoreFunctions.ExpressionLowerer) (fuel : Nat) (scope : Scope)
    (reasonAt : ExpressionId → Word) (callables : SourceCoreFunctions.CallablePolicy)
    {source : TypedSource} {id : ExpressionId} {node : ExpressionNode} {admitted : ExpressionId → Prop} {locals : SourceCoreLocalPolymorphism.Catalog}
    (admission : Admission source admitted) (ordinary : Ordinary source locals context.owner admitted)
    (callerClosed : caller.assumptions = []) (allowed : admitted id)
    (found : source.lookupExpression? id = some node) :
    SourceCoreEvidence.lowerWithProjector checkedProgram projector caller context child fuel source scope id reasonAt callables = .ok none := by
  have requirements := ordinary.requirements id node allowed found
  have coercions := ordinary.coercions id node allowed found
  rcases admission.shape id node allowed found with fragment | composition
  · exact evidence_fragment checkedProgram projector caller context child fuel scope reasonAt callables fragment found requirements coercions
  · have ordinaryOwned : SourceCompilationPlan.ordinaryOwnedRequirements? node = some (CompatibleExpressionLiterals.owned node.form) := by
      unfold SourceCompilationPlan.ordinaryOwnedRequirements?
      rw [requirements, coercions]
      change (if (CompatibleExpressionLiterals.owned node.form).length < 0 then none else
        if CompatibleExpressionLiterals.owned node.form = (CompatibleExpressionLiterals.owned node.form).take
            ((CompatibleExpressionLiterals.owned node.form).length - 0) ++ [] then
          some ((CompatibleExpressionLiterals.owned node.form).take ((CompatibleExpressionLiterals.owned node.form).length - 0)) else none) = _
      simp
    cases form : node.form <;> simp [compositionForm, form] at composition
    case call callee arguments resolution =>
      cases resolution <;> simp [compositionForm] at composition
      all_goals simp [SourceCoreEvidence.lowerWithProjector, found, form, ordinaryOwned, requirements, coercions,
        callerClosed, CompatibleExpressionLiterals.owned, bind, Except.bind, pure, Except.pure]
    all_goals simp [SourceCoreEvidence.lowerWithProjector, found, form, ordinaryOwned, requirements, coercions,
      callerClosed, CompatibleExpressionLiterals.owned, bind, Except.bind, pure, Except.pure]

/-- The production root contextual pass yields the same existing call Tree.
Full inventory/source type/order receipts remain static inputs. The actual
closed caller and ordinary occurrence metadata discharge the special hook;
local specialization and qualified method callers are outside this entry. -/
theorem tree_of_contextual_at
    {checkedProgram : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {signatures : ProgramSignatures} {locals : SourceCoreLocalPolymorphism.Catalog}
    {parents : List SourceCoreLocalEvidence.Prepared} {assignments : SourceCoreAssignmentFaultSites.Table}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {native : SourceCoreGeneralFunctions.CallableContext}
    {skipInitializer : Option ExpressionId} {fuel readFuel : Nat}
    {source : TypedSource} {scope : Scope} {id : ExpressionId} {node : ExpressionNode}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    {sourceContext : SourceSemantics.Context} {admitted : ExpressionId → Prop}
    {caller : SourceSpecialization.SpecializedFunction}
    (admission : Admission source admitted) (coverage : ReachedCoverage headers compilation source admitted)
    (sourceTypes : SourceTypes headers sourceContext)
    (order : ∀ id callee arguments instantiation node, admitted id → source.lookupExpression? id = some node →
      node.form = .call callee arguments (.declaration instantiation) → Ordered compilation.plan instantiation)
    (ordinary : Ordinary source locals compilation.owner admitted)
    (callerSelected : SourceCompilationPlan.exactSpecialization compilation.plan compilation.owner = .ok caller)
    (callerClosed : caller.assumptions = [])
    (unique : NodeOccurrencesUnique source)
    (constructorValid : CompatibleExpressionInstantiationLaws.ConstructorLaw source sourceContext admitted)
    (fragmentValid : CompatibleExpressionInstantiationLaws.ConstructorLaw source sourceContext (CompatibleExpressionBuiltins.Syntax source))
    (selectedValid : SelectedDeclarationLaw headers compilation source sourceContext admitted)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope sourceContext)
    (sourceSignatures : sourceContext.signatures = values.checked.signatures)
    (allowed : admitted id) (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source sourceContext id node.type)
    (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression checkedProgram representation signatures locals parents assignments
      diagnostics compilation (some native) none skipInitializer fuel source scope id reasonAt = .ok lowered) :
    Expressions headers compilation readFuel source sourceContext compilation.solvedRequirements reasonAt scope id lowered := by
  cases fuel with
  | zero => simp [SourceCoreGeneralFunctions.lowerContextualExpression] at accepted
  | succ fuel =>
    rw [SourceCoreGeneralFunctions.lowerContextualExpression.eq_def] at accepted
    dsimp only at accepted
    simp only [callerSelected, Except.mapError, bind, Except.bind, pure, Except.pure] at accepted
    refine tree_of_functions_at admission coverage sourceTypes order unique declarations sourceSignatures constructorValid fragmentValid selectedValid
      ?_ native [] rfl ordinary.fragment.coercions ordinary.coercions allowed found typed accepted
    refine ⟨⟨?_, ?_, lowerPolicy, leafPolicy⟩, ?_, ?_⟩
    · intro childId childTree child budget
      obtain ⟨childNode, childFound⟩ := fragment_has_node childTree
      dsimp only
      rw [contextualSource_fragment checkedProgram compilation.plan locals compilation.owner none ordinary.fragment childTree]
      simp only [bind, Except.bind, pure, Except.pure, childFound, ordinary.fragment.notInitializer _ childTree, Option.filter]
      rw [evidence_fragment checkedProgram _ caller compilation child budget scope reasonAt _ childTree childFound
        (ordinary.fragment.requirements _ _ childTree childFound) (ordinary.fragment.coercions _ _ childTree childFound)]
      cases childForm : childNode.form <;> simp only [childForm]
      case reference name resolution =>
        cases resolution <;> simp only
        case «local» binder =>
          rw [ordinary.fragment.localBinder _ _ _ _ childTree childFound childForm]
          rfl
    · intro childId childTree
      change (do
        let viewed ← SourceCoreGeneralFunctions.contextualSource checkedProgram compilation.plan locals compilation.owner none source childId
        representation.expressions.readExpression viewed childId) = _
      rw [contextualSource_fragment checkedProgram compilation.plan locals compilation.owner none ordinary.fragment childTree]
      simp only [bind, Except.bind, readPolicy]
    · intro childId allowed child budget
      have childFound := admission.found _ allowed
      obtain ⟨childNode, childFound⟩ := childFound
      dsimp only
      rw [contextualSource_admitted checkedProgram compilation.plan locals compilation.owner admission ordinary allowed childFound]
      simp only [bind, Except.bind, pure, Except.pure, childFound, ordinary.notInitializer _ allowed, Option.filter]
      rw [evidence_admitted checkedProgram _ caller compilation child budget scope reasonAt _ admission ordinary callerClosed allowed childFound]
      cases childForm : childNode.form <;> simp only [childForm]
      case reference name resolution =>
        cases resolution <;> simp only
        case «local» binder =>
          rw [ordinary.localBinder _ _ _ _ allowed childFound childForm]
          rfl
    · intro childId allowed
      obtain ⟨childNode, childFound⟩ := admission.found _ allowed
      change (do
        let viewed ← SourceCoreGeneralFunctions.contextualSource checkedProgram compilation.plan locals compilation.owner none source childId
        representation.expressions.readExpression viewed childId) = _
      rw [contextualSource_admitted checkedProgram compilation.plan locals compilation.owner admission ordinary allowed childFound]
      simp only [bind, Except.bind, readPolicy]

/-- Preserve the former whole-inventory interface as a restriction. -/
theorem tree_of_contextual_with_selected_validity
    {checkedProgram : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {signatures : ProgramSignatures} {locals : SourceCoreLocalPolymorphism.Catalog}
    {parents : List SourceCoreLocalEvidence.Prepared} {assignments : SourceCoreAssignmentFaultSites.Table}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {native : SourceCoreGeneralFunctions.CallableContext}
    {skipInitializer : Option ExpressionId} {fuel readFuel : Nat}
    {source : TypedSource} {scope : Scope} {id : ExpressionId} {node : ExpressionNode}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    {sourceContext : SourceSemantics.Context} {admitted : ExpressionId → Prop}
    {caller : SourceSpecialization.SpecializedFunction}
    (admission : Admission source admitted) (coverage : Coverage headers compilation)
    (sourceTypes : SourceTypes headers sourceContext)
    (order : ∀ id callee arguments instantiation node, admitted id → source.lookupExpression? id = some node →
      node.form = .call callee arguments (.declaration instantiation) → Ordered compilation.plan instantiation)
    (ordinary : Ordinary source locals compilation.owner admitted)
    (callerSelected : SourceCompilationPlan.exactSpecialization compilation.plan compilation.owner = .ok caller)
    (callerClosed : caller.assumptions = [])
    (unique : NodeOccurrencesUnique source)
    (constructorValid : CompatibleExpressionInstantiationLaws.ConstructorLaw source sourceContext admitted)
    (fragmentValid : CompatibleExpressionInstantiationLaws.ConstructorLaw source sourceContext (CompatibleExpressionBuiltins.Syntax source))
    (selectedValid : SelectedDeclarationLaw headers compilation source sourceContext admitted)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope sourceContext)
    (sourceSignatures : sourceContext.signatures = values.checked.signatures)
    (allowed : admitted id) (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source sourceContext id node.type)
    (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression checkedProgram representation signatures locals parents assignments
      diagnostics compilation (some native) none skipInitializer fuel source scope id reasonAt = .ok lowered) :
    Expressions headers compilation readFuel source sourceContext compilation.solvedRequirements reasonAt scope id lowered := by
  exact tree_of_contextual_at admission coverage.restrict sourceTypes order ordinary callerSelected callerClosed
    unique constructorValid fragmentValid selectedValid declarations sourceSignatures allowed found typed readPolicy lowerPolicy leafPolicy accepted

/-- Preserve the original all-admitted-site interface as a restriction adapter. -/
theorem tree_of_contextual_with_validity
    {checkedProgram : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {signatures : ProgramSignatures} {locals : SourceCoreLocalPolymorphism.Catalog}
    {parents : List SourceCoreLocalEvidence.Prepared} {assignments : SourceCoreAssignmentFaultSites.Table}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {native : SourceCoreGeneralFunctions.CallableContext}
    {skipInitializer : Option ExpressionId} {fuel readFuel : Nat}
    {source : TypedSource} {scope : Scope} {id : ExpressionId} {node : ExpressionNode}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    {sourceContext : SourceSemantics.Context} {admitted : ExpressionId → Prop}
    {caller : SourceSpecialization.SpecializedFunction}
    (admission : Admission source admitted) (coverage : Coverage headers compilation)
    (sourceTypes : SourceTypes headers sourceContext)
    (order : ∀ id callee arguments instantiation node, admitted id → source.lookupExpression? id = some node →
      node.form = .call callee arguments (.declaration instantiation) → Ordered compilation.plan instantiation)
    (ordinary : Ordinary source locals compilation.owner admitted)
    (callerSelected : SourceCompilationPlan.exactSpecialization compilation.plan compilation.owner = .ok caller)
    (callerClosed : caller.assumptions = [])
    (unique : NodeOccurrencesUnique source)
    (constructorValid : CompatibleExpressionInstantiationLaws.ConstructorLaw source sourceContext admitted)
    (fragmentValid : CompatibleExpressionInstantiationLaws.ConstructorLaw source sourceContext (CompatibleExpressionBuiltins.Syntax source))
    (declarationValid : CompatibleExpressionInstantiationLaws.DeclarationLaw source sourceContext admitted)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope sourceContext)
    (sourceSignatures : sourceContext.signatures = values.checked.signatures)
    (allowed : admitted id) (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source sourceContext id node.type)
    (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression checkedProgram representation signatures locals parents assignments
      diagnostics compilation (some native) none skipInitializer fuel source scope id reasonAt = .ok lowered) :
    Expressions headers compilation readFuel source sourceContext compilation.solvedRequirements reasonAt scope id lowered := by
  exact tree_of_contextual_with_selected_validity (checkedProgram := checkedProgram)
    (representation := representation) (signatures := signatures) (locals := locals) (parents := parents)
    (assignments := assignments) (diagnostics := diagnostics) (native := native)
    (skipInitializer := skipInitializer) (fuel := fuel) (readFuel := readFuel) (source := source) (scope := scope)
    (id := id) (node := node) (reasonAt := reasonAt) (lowered := lowered) (sourceContext := sourceContext)
    (admitted := admitted) (caller := caller) (admission := admission) (coverage := coverage)
    (sourceTypes := sourceTypes) (order := order) (ordinary := ordinary) (callerSelected := callerSelected)
    (callerClosed := callerClosed) (unique := unique) (constructorValid := constructorValid)
    (fragmentValid := fragmentValid) (selectedValid := SelectedDeclarationLaw.of_declaration declarationValid)
    (declarations := declarations) (sourceSignatures := sourceSignatures) (allowed := allowed) (found := found)
    (typed := typed) (readPolicy := readPolicy) (lowerPolicy := lowerPolicy) (leafPolicy := leafPolicy)
    (accepted := accepted)

/-- Compatibility with the former false residual scope. -/
theorem tree_of_contextual
    {checkedProgram : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {signatures : ProgramSignatures} {locals : SourceCoreLocalPolymorphism.Catalog}
    {parents : List SourceCoreLocalEvidence.Prepared} {assignments : SourceCoreAssignmentFaultSites.Table}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {native : SourceCoreGeneralFunctions.CallableContext}
    {skipInitializer : Option ExpressionId} {fuel readFuel : Nat}
    {source : TypedSource} {scope : Scope} {id : ExpressionId} {node : ExpressionNode}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    {sourceContext : SourceSemantics.Context} {admitted : ExpressionId → Prop}
    {caller : SourceSpecialization.SpecializedFunction}
    (admission : Admission source admitted) (coverage : Coverage headers compilation)
    (sourceTypes : SourceTypes headers sourceContext)
    (order : ∀ id callee arguments instantiation node, admitted id → source.lookupExpression? id = some node →
      node.form = .call callee arguments (.declaration instantiation) → Ordered compilation.plan instantiation)
    (ordinary : Ordinary source locals compilation.owner admitted)
    (callerSelected : SourceCompilationPlan.exactSpecialization compilation.plan compilation.owner = .ok caller)
    (callerClosed : caller.assumptions = [])
    (unique : NodeOccurrencesUnique source)
    (closed : sourceContext.typeVariables = []) (residual : sourceContext.residualTypeVariables = false)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope sourceContext)
    (sourceSignatures : sourceContext.signatures = values.checked.signatures)
    (allowed : admitted id) (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source sourceContext id node.type)
    (readPolicy : representation.expressions.readExpression = SourceCoreCompatibleDataExpressions.readExpression values.checked)
    (lowerPolicy : representation.expressions.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values)
    (leafPolicy : representation.expressions.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression checkedProgram representation signatures locals parents assignments
      diagnostics compilation (some native) none skipInitializer fuel source scope id reasonAt = .ok lowered) :
    Expressions headers compilation readFuel source sourceContext compilation.solvedRequirements reasonAt scope id lowered := by
  exact tree_of_contextual_with_validity (checkedProgram := checkedProgram) (representation := representation)
    (signatures := signatures) (locals := locals) (parents := parents) (assignments := assignments)
    (diagnostics := diagnostics) (native := native) (skipInitializer := skipInitializer) (fuel := fuel)
    (readFuel := readFuel) (source := source) (scope := scope) (id := id) (node := node) (reasonAt := reasonAt)
    (lowered := lowered) (sourceContext := sourceContext) (admitted := admitted) (caller := caller)
    (admission := admission) (coverage := coverage) (sourceTypes := sourceTypes) (order := order)
    (ordinary := ordinary) (callerSelected := callerSelected) (callerClosed := callerClosed) (unique := unique)
    (constructorValid := CompatibleExpressionInstantiationLaws.ConstructorLaw.of_closed closed residual)
    (fragmentValid := CompatibleExpressionInstantiationLaws.ConstructorLaw.of_closed closed residual)
    (declarationValid := CompatibleExpressionInstantiationLaws.DeclarationLaw.of_closed closed residual)
    (declarations := declarations) (sourceSignatures := sourceSignatures) (allowed := allowed) (found := found)
    (typed := typed) (readPolicy := readPolicy) (lowerPolicy := lowerPolicy) (leafPolicy := leafPolicy)
    (accepted := accepted)

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionCompilerCertificates
