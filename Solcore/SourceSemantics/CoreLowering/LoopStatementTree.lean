import Solcore.SourceSemantics.CoreLowering.BasicStatementTreeCertificates
import Solcore.Frontend.SourceCoreLoops

/-! Static certificates for the default scalar/product while-loop profile.
The source tree describes syntax and checked metadata, not termination.
Finite executions will be related through independent source derivations.
For-header traversal is a separate extension; this initial grammar has while
loops, break and continue, without named calls or source closures. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.LoopStatements.Default

open Frontend Frontend.SourceInference TypeSystem LocalCell BasicStatements

/-- A finite control statement tree. `tailReturns` marks function sequencing;
nested blocks and conditional branches use ordinary statement sequencing. -/
inductive Tree (compilation : SourceCorePrimitive.Context) (source : TypedSource)
    (reasonAt : ExpressionId → Core.Word) (selfReason : Core.Word) :
    SourceCoreLocalCell.Scope → Context → Bool → List StatementId → Core.Ty → Core.Expr → Prop where
  | nil {scope context tailReturns type} :
      Tree compilation source reasonAt selfReason scope context tailReturns [] type (Core.LocalLoop.fallthrough type)
  | letUninitialized
      {scope context middleContext tailReturns id rest node binder payloadType resultType body}
      (metadata : Metadata source id node .unit)
      (form : node.form = .letDecl binder none)
      (binding : BinderCertificate source scope binder payloadType)
      (extension : BinderExtends source.owner context binder middleContext)
      (tail : Tree compilation source reasonAt selfReason ((binder.id, payloadType) :: scope) middleContext
        tailReturns rest resultType body) :
      Tree compilation source reasonAt selfReason scope context tailReturns (id :: rest) resultType
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
        tailReturns rest resultType body) :
      Tree compilation source reasonAt selfReason scope context tailReturns (id :: rest) resultType
        (Core.LocalSequence.letInitialized (Core.LocalLoop.controlType resultType) payloadType initializerCode body)
  | assign
      {scope context tailReturns id rest node assignment index payloadType resultType rhs rhsCode body rhsDepth}
      (metadata : Metadata source id node .unit)
      (form : node.form = .assignValue assignment .equal rhs)
      (target : AssignmentCertificate source scope assignment .equal index payloadType)
      (value : PrimitiveExpressions.Tree compilation source scope reasonAt rhs payloadType rhsCode rhsDepth)
      (tail : Tree compilation source reasonAt selfReason scope context tailReturns rest resultType body) :
      Tree compilation source reasonAt selfReason scope context tailReturns (id :: rest) resultType
        (Core.LocalSequence.assign (Core.LocalLoop.controlType resultType) (.var index) rhsCode body)
  | discard
      {scope context tailReturns id rest node nodeType valueId valueType resultType valueCode body valueDepth semicolon}
      (metadata : Metadata source id node nodeType)
      (form : node.form = .expression valueId semicolon)
      (notTail : (!semicolon && tailReturns && rest.isEmpty) = false)
      (statementType : if semicolon then nodeType = .unit else nodeType = valueType)
      (value : PrimitiveExpressions.Tree compilation source scope reasonAt valueId valueType valueCode valueDepth)
      (tail : Tree compilation source reasonAt selfReason scope context tailReturns rest resultType body) :
      Tree compilation source reasonAt selfReason scope context tailReturns (id :: rest) resultType
        (Core.LocalSequence.discard (Core.LocalLoop.controlType resultType) valueCode body)
  | returnValue
      {scope context tailReturns id node valueId resultType valueCode valueDepth}
      (rest : List StatementId)
      (metadata : Metadata source id node resultType)
      (form : node.form = .returnStmt (some valueId))
      (value : PrimitiveExpressions.Tree compilation source scope reasonAt valueId resultType valueCode valueDepth) :
      Tree compilation source reasonAt selfReason scope context tailReturns (id :: rest) resultType
        (Core.LocalLoop.returnValue resultType valueCode)
  | returnUnit {scope context tailReturns id node}
      (rest : List StatementId)
      (metadata : Metadata source id node .unit)
      (form : node.form = .returnStmt none) :
      Tree compilation source reasonAt selfReason scope context tailReturns (id :: rest) .unit (Core.LocalLoop.returned .unit)
  | tailExpression
      {scope context id node valueId resultType valueCode valueDepth}
      (metadata : Metadata source id node resultType)
      (form : node.form = .expression valueId false)
      (value : PrimitiveExpressions.Tree compilation source scope reasonAt valueId resultType valueCode valueDepth) :
      Tree compilation source reasonAt selfReason scope context true [id] resultType (Core.LocalLoop.returnValue resultType valueCode)
  | block
      {scope context tailReturns id rest node nodeType statements resultType blockCode body}
      (metadata : Metadata source id node nodeType)
      (form : node.form = .block statements)
      (block : Tree compilation source reasonAt selfReason scope context false statements resultType blockCode)
      (tail : Tree compilation source reasonAt selfReason scope context tailReturns rest resultType body) :
      Tree compilation source reasonAt selfReason scope context tailReturns (id :: rest) resultType
        (Core.LocalLoop.sequence resultType blockCode body)
  | ifThen
      {scope context tailReturns id rest node nodeType condition thenBody elseBody resultType
        conditionCode thenCode elseCode body conditionDepth}
      (metadata : Metadata source id node nodeType)
      (form : node.form = .ifThen condition thenBody elseBody)
      (conditionTree : PrimitiveExpressions.Tree compilation source scope reasonAt condition .bool conditionCode conditionDepth)
      (thenTree : Tree compilation source reasonAt selfReason scope context false thenBody resultType thenCode)
      (elseTree : Tree compilation source reasonAt selfReason scope context false (elseBody.getD []) resultType elseCode)
      (tail : Tree compilation source reasonAt selfReason scope context tailReturns rest resultType body) :
      Tree compilation source reasonAt selfReason scope context tailReturns (id :: rest) resultType
        (Core.LocalLoop.sequence resultType
          (Core.LocalLoop.conditional resultType conditionCode thenCode elseCode) body)

  | whileLoop
      {scope context tailReturns id rest node condition statements resultType conditionCode bodyCode body conditionDepth}
      (metadata : Metadata source id node .unit)
      (form : node.form = .whileLoop condition statements)
      (conditionTree : PrimitiveExpressions.Tree compilation source scope reasonAt condition .bool conditionCode conditionDepth)
      (loopBody : Tree compilation source reasonAt selfReason scope context false statements resultType bodyCode)
      (tail : Tree compilation source reasonAt selfReason scope context tailReturns rest resultType body) :
      Tree compilation source reasonAt selfReason scope context tailReturns (id :: rest) resultType
        (Core.LocalLoop.sequence resultType (Core.LocalLoop.whileLoop resultType conditionCode bodyCode selfReason) body)
  | breaking {scope context tailReturns id node resultType}
      (rest : List StatementId) (metadata : Metadata source id node .unit) (form : node.form = .breakStmt) :
      Tree compilation source reasonAt selfReason scope context tailReturns (id :: rest) resultType
        (Core.LocalLoop.breaking resultType)
  | continuing {scope context tailReturns id node resultType}
      (rest : List StatementId) (metadata : Metadata source id node .unit) (form : node.form = .continueStmt) :
      Tree compilation source reasonAt selfReason scope context tailReturns (id :: rest) resultType
        (Core.LocalLoop.continuing resultType)

theorem Tree.hasType
    {compilation : SourceCorePrimitive.Context} {source : TypedSource}
    {reasonAt : ExpressionId → Core.Word} {selfReason : Core.Word} {scope : SourceCoreLocalCell.Scope}
    {context : Context} {tailReturns : Bool} {statements : List StatementId} {type : Core.Ty} {code : Core.Expr}
    (tree : Tree compilation source reasonAt selfReason scope context tailReturns statements type code)
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

end Solcore.SourceSemantics.CoreLowering.LoopStatements.Default
