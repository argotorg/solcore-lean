import Solcore.SourceSemantics.CoreLowering.ForHeaderTree
import Solcore.Frontend.SourceCoreLoops

/-! Static certificates for the complete default scalar/product loop profile.
Statement lists and initializer vectors are separate indices of one tree, so
structural induction traverses a nested loop body without any evaluation
hypothesis or an additional mutually recursive semantics. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.LoopStatements.WithFor

open Frontend Frontend.SourceInference TypeSystem LocalCell BasicStatements

inductive Position where
  | statements (tailReturns : Bool) (statements : List StatementId)
  | initializers (items : List ForItemForm) (condition : ExpressionId)
      (post : List ForItemForm) (statements : List StatementId)

/-- A finite control statement tree. `tailReturns` marks function sequencing;
nested blocks and conditional branches use ordinary statement sequencing. -/
inductive Tree (compilation : SourceCorePrimitive.Context) (source : TypedSource)
    (reasonAt : ExpressionId → Core.Word) (selfReason : Core.Word) :
    SourceCoreLocalCell.Scope → Context → Position → Core.Ty → Core.Expr → Prop where
  | nil {scope context tailReturns type} :
      Tree compilation source reasonAt selfReason scope context (.statements tailReturns []) type (Core.LocalLoop.fallthrough type)
  | letUninitialized
      {scope context middleContext tailReturns id rest node binder payloadType resultType body}
      (metadata : Metadata source id node .unit)
      (form : node.form = .letDecl binder none)
      (binding : BinderCertificate source scope binder payloadType)
      (extension : BinderExtends source.owner context binder middleContext)
      (tail : Tree compilation source reasonAt selfReason ((binder.id, payloadType) :: scope) middleContext
        (.statements tailReturns rest) resultType body) :
      Tree compilation source reasonAt selfReason scope context (.statements tailReturns (id :: rest)) resultType
        (Core.LocalSequence.letUninitialized payloadType body)
  | letInitialized
      {scope context middleContext tailReturns id rest node binder payloadType resultType
        initializer initializerCode body initializerDepth}
      (metadata : Metadata source id node .unit)
      (form : node.form = .letDecl binder (some initializer))
      (binding : BinderCertificate source scope binder payloadType)
      (extension : BinderExtends source.owner context binder middleContext)
      (value : PrimitiveExpressions.Tree compilation source scope reasonAt initializer payloadType initializerCode initializerDepth)
      (tail : Tree compilation source reasonAt selfReason ((binder.id, payloadType) :: scope) middleContext
        (.statements tailReturns rest) resultType body) :
      Tree compilation source reasonAt selfReason scope context (.statements tailReturns (id :: rest)) resultType
        (Core.LocalSequence.letInitialized (Core.LocalLoop.controlType resultType) payloadType initializerCode body)
  | assign
      {scope context tailReturns id rest node assignment index payloadType resultType rhs rhsCode body rhsDepth}
      (metadata : Metadata source id node .unit)
      (form : node.form = .assignValue assignment .equal rhs)
      (target : AssignmentCertificate source scope assignment .equal index payloadType)
      (value : PrimitiveExpressions.Tree compilation source scope reasonAt rhs payloadType rhsCode rhsDepth)
      (tail : Tree compilation source reasonAt selfReason scope context (.statements tailReturns rest) resultType body) :
      Tree compilation source reasonAt selfReason scope context (.statements tailReturns (id :: rest)) resultType
        (Core.LocalSequence.assign (Core.LocalLoop.controlType resultType) (.var index) rhsCode body)
  | discard
      {scope context tailReturns id rest node nodeType valueId valueType resultType valueCode body valueDepth semicolon}
      (metadata : Metadata source id node nodeType)
      (form : node.form = .expression valueId semicolon)
      (notTail : (!semicolon && tailReturns && rest.isEmpty) = false)
      (statementType : if semicolon then nodeType = .unit else nodeType = valueType)
      (value : PrimitiveExpressions.Tree compilation source scope reasonAt valueId valueType valueCode valueDepth)
      (tail : Tree compilation source reasonAt selfReason scope context (.statements tailReturns rest) resultType body) :
      Tree compilation source reasonAt selfReason scope context (.statements tailReturns (id :: rest)) resultType
        (Core.LocalSequence.discard (Core.LocalLoop.controlType resultType) valueCode body)
  | returnValue
      {scope context tailReturns id node valueId resultType valueCode valueDepth}
      (rest : List StatementId)
      (metadata : Metadata source id node resultType)
      (form : node.form = .returnStmt (some valueId))
      (value : PrimitiveExpressions.Tree compilation source scope reasonAt valueId resultType valueCode valueDepth) :
      Tree compilation source reasonAt selfReason scope context (.statements tailReturns (id :: rest)) resultType
        (Core.LocalLoop.returnValue resultType valueCode)
  | returnUnit {scope context tailReturns id node}
      (rest : List StatementId)
      (metadata : Metadata source id node .unit)
      (form : node.form = .returnStmt none) :
      Tree compilation source reasonAt selfReason scope context (.statements tailReturns (id :: rest)) .unit (Core.LocalLoop.returned .unit)
  | tailExpression
      {scope context id node valueId resultType valueCode valueDepth}
      (metadata : Metadata source id node resultType)
      (form : node.form = .expression valueId false)
      (value : PrimitiveExpressions.Tree compilation source scope reasonAt valueId resultType valueCode valueDepth) :
      Tree compilation source reasonAt selfReason scope context (.statements true [id]) resultType (Core.LocalLoop.returnValue resultType valueCode)
  | block
      {scope context tailReturns id rest node nodeType statements resultType blockCode body}
      (metadata : Metadata source id node nodeType)
      (form : node.form = .block statements)
      (block : Tree compilation source reasonAt selfReason scope context (.statements false statements) resultType blockCode)
      (tail : Tree compilation source reasonAt selfReason scope context (.statements tailReturns rest) resultType body) :
      Tree compilation source reasonAt selfReason scope context (.statements tailReturns (id :: rest)) resultType
        (Core.LocalLoop.sequence resultType blockCode body)
  | ifThen
      {scope context tailReturns id rest node nodeType condition thenBody elseBody resultType
        conditionCode thenCode elseCode body conditionDepth}
      (metadata : Metadata source id node nodeType)
      (form : node.form = .ifThen condition thenBody elseBody)
      (conditionTree : PrimitiveExpressions.Tree compilation source scope reasonAt condition .bool conditionCode conditionDepth)
      (thenTree : Tree compilation source reasonAt selfReason scope context (.statements false thenBody) resultType thenCode)
      (elseTree : Tree compilation source reasonAt selfReason scope context (.statements false (elseBody.getD [])) resultType elseCode)
      (tail : Tree compilation source reasonAt selfReason scope context (.statements tailReturns rest) resultType body) :
      Tree compilation source reasonAt selfReason scope context (.statements tailReturns (id :: rest)) resultType
        (Core.LocalLoop.sequence resultType
          (Core.LocalLoop.conditional resultType conditionCode thenCode elseCode) body)

  | whileLoop
      {scope context tailReturns id rest node condition statements resultType conditionCode bodyCode body conditionDepth}
      (metadata : Metadata source id node .unit)
      (form : node.form = .whileLoop condition statements)
      (conditionTree : PrimitiveExpressions.Tree compilation source scope reasonAt condition .bool conditionCode conditionDepth)
      (loopBody : Tree compilation source reasonAt selfReason scope context (.statements false statements) resultType bodyCode)
      (tail : Tree compilation source reasonAt selfReason scope context (.statements tailReturns rest) resultType body) :
      Tree compilation source reasonAt selfReason scope context (.statements tailReturns (id :: rest)) resultType
        (Core.LocalLoop.sequence resultType (Core.LocalLoop.whileLoop resultType conditionCode bodyCode selfReason) body)
  | forLoop
      {scope context tailReturns id rest node initializer condition post statements resultType loopCode body}
      (metadata : Metadata source id node .unit)
      (form : node.form = .forLoop initializer condition post statements)
      (initialTree : Tree compilation source reasonAt selfReason scope context
        (.initializers initializer condition post statements) resultType loopCode)
      (tail : Tree compilation source reasonAt selfReason scope context (.statements tailReturns rest) resultType body) :
      Tree compilation source reasonAt selfReason scope context (.statements tailReturns (id :: rest)) resultType
        (Core.LocalLoop.sequence resultType loopCode body)
  | initializersDone
      {scope context condition post statements resultType conditionCode bodyCode postCode depth}
      (conditionTree : PrimitiveExpressions.Tree compilation source scope reasonAt condition .bool conditionCode depth)
      (bodyTree : Tree compilation source reasonAt selfReason scope context (.statements false statements) resultType bodyCode)
      (postTree : ForHeaders.Tree compilation source reasonAt resultType (ForHeaders.Fallthrough resultType) scope context post postCode) :
      Tree compilation source reasonAt selfReason scope context (.initializers [] condition post statements) resultType
        (Core.LocalLoop.iterate resultType conditionCode bodyCode postCode selfReason)
  | initializerUninitialized
      {scope context middleContext binder rest condition post statements payloadType resultType body}
      (binding : BinderCertificate source scope binder payloadType)
      (extension : BinderExtends source.owner context binder middleContext)
      (tail : Tree compilation source reasonAt selfReason ((binder.id, payloadType) :: scope) middleContext
        (.initializers rest condition post statements) resultType body) :
      Tree compilation source reasonAt selfReason scope context (.initializers (.letDecl binder none :: rest) condition post statements) resultType
        (Core.LocalSequence.letUninitialized payloadType body)
  | initializerInitialized
      {scope context middleContext binder rest condition post statements payloadType resultType initializer initializerCode body depth}
      (binding : BinderCertificate source scope binder payloadType)
      (extension : BinderExtends source.owner context binder middleContext)
      (value : PrimitiveExpressions.Tree compilation source scope reasonAt initializer payloadType initializerCode depth)
      (tail : Tree compilation source reasonAt selfReason ((binder.id, payloadType) :: scope) middleContext
        (.initializers rest condition post statements) resultType body) :
      Tree compilation source reasonAt selfReason scope context (.initializers (.letDecl binder (some initializer) :: rest) condition post statements) resultType
        (Core.LocalSequence.letInitialized (Core.LocalLoop.controlType resultType) payloadType initializerCode body)
  | initializerAssign
      {scope context assignment index payloadType rhs rhsCode rest condition post statements resultType body depth}
      (target : AssignmentCertificate source scope assignment .equal index payloadType)
      (value : PrimitiveExpressions.Tree compilation source scope reasonAt rhs payloadType rhsCode depth)
      (tail : Tree compilation source reasonAt selfReason scope context (.initializers rest condition post statements) resultType body) :
      Tree compilation source reasonAt selfReason scope context (.initializers (.assignValue assignment .equal rhs :: rest) condition post statements) resultType
        (Core.LocalSequence.assign (Core.LocalLoop.controlType resultType) (.var index) rhsCode body)
  | initializerDiscard
      {scope context expression expressionType expressionCode rest condition post statements resultType body depth}
      (value : PrimitiveExpressions.Tree compilation source scope reasonAt expression expressionType expressionCode depth)
      (tail : Tree compilation source reasonAt selfReason scope context (.initializers rest condition post statements) resultType body) :
      Tree compilation source reasonAt selfReason scope context (.initializers (.expression expression :: rest) condition post statements) resultType
        (Core.LocalSequence.discard (Core.LocalLoop.controlType resultType) expressionCode body)
  | breaking {scope context tailReturns id node resultType}
      (rest : List StatementId) (metadata : Metadata source id node .unit) (form : node.form = .breakStmt) :
      Tree compilation source reasonAt selfReason scope context (.statements tailReturns (id :: rest)) resultType
        (Core.LocalLoop.breaking resultType)
  | continuing {scope context tailReturns id node resultType}
      (rest : List StatementId) (metadata : Metadata source id node .unit) (form : node.form = .continueStmt) :
      Tree compilation source reasonAt selfReason scope context (.statements tailReturns (id :: rest)) resultType
        (Core.LocalLoop.continuing resultType)

theorem Tree.hasType
    {compilation : SourceCorePrimitive.Context} {source : TypedSource}
    {reasonAt : ExpressionId → Core.Word} {selfReason : Core.Word} {scope : SourceCoreLocalCell.Scope}
    {context : Context} {position : Position} {type : Core.Ty} {code : Core.Expr}
    (tree : Tree compilation source reasonAt selfReason scope context position type code)
    (wellFormed : Core.Ty.WellFormed [] type) :
    Core.HasType (SourceCoreLocalCell.coreContext scope) code (Core.LocalLoop.resultType type) := by
  induction tree with
  | nil => exact Core.LocalLoop.fallthrough_hasType wellFormed
  | returnUnit => exact Core.LocalLoop.returned_hasType .unit
  | breaking => exact Core.LocalLoop.breaking_hasType wellFormed
  | continuing => exact Core.LocalLoop.continuing_hasType wellFormed
  | returnValue _ _ _ value | tailExpression _ _ value =>
      exact Core.LocalLoop.returnValue_hasType wellFormed value.hasType
  | letUninitialized _ _ binding _ _ tail =>
      exact Core.LocalSequence.letUninitialized_hasType (binding.types.wellFormed []) (tail wellFormed)
  | letInitialized _ _ _ _ value _ tail =>
      exact Core.LocalSequence.letInitialized_hasType (Core.LocalLoop.controlType_wellFormed wellFormed) value.hasType (tail wellFormed)
  | assign _ _ target value _ tail =>
      exact Core.LocalSequence.assign_hasType (Core.LocalLoop.controlType_wellFormed wellFormed)
        (.var (SourceCoreLocalCell.lookup?_context target.slot)) value.hasType (tail wellFormed)
  | discard _ _ _ _ value _ tail =>
      exact Core.LocalSequence.discard_hasType (Core.LocalLoop.controlType_wellFormed wellFormed) value.hasType (tail wellFormed)
  | block _ _ _ _ block tail => exact Core.LocalLoop.sequence_hasType wellFormed (block wellFormed) (tail wellFormed)
  | ifThen _ _ condition _ _ _ thenTree elseTree tail =>
      exact Core.LocalLoop.sequence_hasType wellFormed
        (Core.LocalLoop.conditional_hasType wellFormed condition.hasType (thenTree wellFormed) (elseTree wellFormed))
        (tail wellFormed)

  | whileLoop _ _ condition _ _ loopBody tail =>
      exact Core.LocalLoop.sequence_hasType wellFormed
        (Core.LocalLoop.whileLoop_hasType selfReason wellFormed condition.hasType (loopBody wellFormed))
        (tail wellFormed)

  | forLoop _ _ _ _ initial tail =>
      exact Core.LocalLoop.sequence_hasType wellFormed (initial wellFormed) (tail wellFormed)
  | initializersDone condition _ post body =>
      apply Core.LocalLoop.iterate_hasType selfReason wellFormed condition.hasType (body wellFormed)
      apply post.hasType wellFormed
      intro scope context code endpoint
      cases endpoint
      exact Core.LocalLoop.fallthrough_hasType wellFormed
  | initializerUninitialized binding _ _ tail =>
      exact Core.LocalSequence.letUninitialized_hasType (binding.types.wellFormed []) (tail wellFormed)
  | initializerInitialized _ _ value _ tail =>
      exact Core.LocalSequence.letInitialized_hasType (Core.LocalLoop.controlType_wellFormed wellFormed) value.hasType (tail wellFormed)
  | initializerAssign target value _ tail =>
      exact Core.LocalSequence.assign_hasType (Core.LocalLoop.controlType_wellFormed wellFormed)
        (.var (SourceCoreLocalCell.lookup?_context target.slot)) value.hasType (tail wellFormed)
  | initializerDiscard value _ tail =>
      exact Core.LocalSequence.discard_hasType (Core.LocalLoop.controlType_wellFormed wellFormed) value.hasType (tail wellFormed)

/-- Generic header acceptance can authenticate the empty-header continuation
first, then reconstruct every initializer binder and expression around it. -/
theorem Tree.ofHeader
    {compilation : SourceCorePrimitive.Context} {source : TypedSource} {reasonAt : ExpressionId → Core.Word}
    {selfReason : Core.Word} {scope : SourceCoreLocalCell.Scope} {context : Context} {items post : List ForItemForm}
    {condition : ExpressionId} {statements : List StatementId} {type : Core.Ty} {code : Core.Expr}
    (header : ForHeaders.Tree compilation source reasonAt type
      (fun scope context code => Tree compilation source reasonAt selfReason scope context (.initializers [] condition post statements) type code)
      scope context items code) :
    Tree compilation source reasonAt selfReason scope context (.initializers items condition post statements) type code := by
  induction header with
  | nil next => exact next
  | letUninitialized binding extension _ tail => exact .initializerUninitialized binding extension tail
  | letInitialized binding extension value _ tail => exact .initializerInitialized binding extension value tail
  | assign target value _ tail => exact .initializerAssign target value tail
  | discard value _ tail => exact .initializerDiscard value tail


end Solcore.SourceSemantics.CoreLowering.LoopStatements.WithFor
