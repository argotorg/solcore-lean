import Solcore.SourceSemantics.CoreLowering.BasicStatementTreeCertificates

/-! Static certificates for scoped control statements. Function lists and
nested lists differ only in their final-expression convention. The certificates
contain no child evaluation premise and preserve the actual reason provider. -/

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.ControlStatements

open Frontend Frontend.SourceInference TypeSystem LocalCell BasicStatements

/-- A finite control statement tree. `tailReturns` marks function sequencing;
nested blocks and conditional branches use ordinary statement sequencing. -/
inductive Tree (source : TypedSource) (reasonAt : ExpressionId → Core.Word) :
    SourceCoreLocalCell.Scope → Context → Bool → List StatementId → Core.Ty → Core.Expr → Prop where
  | nil {scope context tailReturns type} :
      Tree source reasonAt scope context tailReturns [] type (Core.LocalControl.fallthrough type)
  | letUninitialized
      {scope context middleContext tailReturns id rest node binder payloadType resultType body}
      (metadata : Metadata source id node .unit)
      (form : node.form = .letDecl binder none)
      (binding : BinderCertificate source scope binder payloadType)
      (extension : BinderExtends source.owner context binder middleContext)
      (tail : Tree source reasonAt ((binder.id, payloadType) :: scope) middleContext
        tailReturns rest resultType body) :
      Tree source reasonAt scope context tailReturns (id :: rest) resultType
        (Core.LocalSequence.letUninitialized payloadType body)
  | letInitialized
      {scope context middleContext tailReturns id rest node binder payloadType resultType
        initializer initializerCode body initializerDepth}
      (metadata : Metadata source id node .unit)
      (form : node.form = .letDecl binder (some initializer))
      (binding : BinderCertificate source scope binder payloadType)
      (extension : BinderExtends source.owner context binder middleContext)
      (value : ControlExpressions.Tree source scope reasonAt initializer payloadType initializerCode initializerDepth)
      (tail : Tree source reasonAt ((binder.id, payloadType) :: scope) middleContext
        tailReturns rest resultType body) :
      Tree source reasonAt scope context tailReturns (id :: rest) resultType
        (Core.LocalSequence.letInitialized (Core.LocalControl.controlType resultType) payloadType initializerCode body)
  | assign
      {scope context tailReturns id rest node assignment index payloadType resultType rhs rhsCode body rhsDepth}
      (metadata : Metadata source id node .unit)
      (form : node.form = .assignValue assignment .equal rhs)
      (target : AssignmentCertificate source scope assignment .equal index payloadType)
      (value : ControlExpressions.Tree source scope reasonAt rhs payloadType rhsCode rhsDepth)
      (tail : Tree source reasonAt scope context tailReturns rest resultType body) :
      Tree source reasonAt scope context tailReturns (id :: rest) resultType
        (Core.LocalSequence.assign (Core.LocalControl.controlType resultType) (.var index) rhsCode body)
  | discard
      {scope context tailReturns id rest node nodeType valueId valueType resultType valueCode body valueDepth semicolon}
      (metadata : Metadata source id node nodeType)
      (form : node.form = .expression valueId semicolon)
      (notTail : (!semicolon && tailReturns && rest.isEmpty) = false)
      (statementType : if semicolon then nodeType = .unit else nodeType = valueType)
      (value : ControlExpressions.Tree source scope reasonAt valueId valueType valueCode valueDepth)
      (tail : Tree source reasonAt scope context tailReturns rest resultType body) :
      Tree source reasonAt scope context tailReturns (id :: rest) resultType
        (Core.LocalSequence.discard (Core.LocalControl.controlType resultType) valueCode body)
  | returnValue
      {scope context tailReturns id node valueId resultType valueCode valueDepth}
      (rest : List StatementId)
      (metadata : Metadata source id node resultType)
      (form : node.form = .returnStmt (some valueId))
      (value : ControlExpressions.Tree source scope reasonAt valueId resultType valueCode valueDepth) :
      Tree source reasonAt scope context tailReturns (id :: rest) resultType
        (Core.LocalControl.returnValue resultType valueCode)
  | returnUnit {scope context tailReturns id node}
      (rest : List StatementId)
      (metadata : Metadata source id node .unit)
      (form : node.form = .returnStmt none) :
      Tree source reasonAt scope context tailReturns (id :: rest) .unit (Core.LocalControl.returned .unit)
  | tailExpression
      {scope context id node valueId resultType valueCode valueDepth}
      (metadata : Metadata source id node resultType)
      (form : node.form = .expression valueId false)
      (value : ControlExpressions.Tree source scope reasonAt valueId resultType valueCode valueDepth) :
      Tree source reasonAt scope context true [id] resultType (Core.LocalControl.returnValue resultType valueCode)
  | block
      {scope context tailReturns id rest node nodeType statements resultType blockCode body}
      (metadata : Metadata source id node nodeType)
      (form : node.form = .block statements)
      (block : Tree source reasonAt scope context false statements resultType blockCode)
      (tail : Tree source reasonAt scope context tailReturns rest resultType body) :
      Tree source reasonAt scope context tailReturns (id :: rest) resultType
        (Core.LocalControl.sequence resultType blockCode body)
  | ifThen
      {scope context tailReturns id rest node nodeType condition thenBody elseBody resultType
        conditionCode thenCode elseCode body conditionDepth}
      (metadata : Metadata source id node nodeType)
      (form : node.form = .ifThen condition thenBody elseBody)
      (conditionTree : ControlExpressions.Tree source scope reasonAt condition .bool conditionCode conditionDepth)
      (thenTree : Tree source reasonAt scope context false thenBody resultType thenCode)
      (elseTree : Tree source reasonAt scope context false (elseBody.getD []) resultType elseCode)
      (tail : Tree source reasonAt scope context tailReturns rest resultType body) :
      Tree source reasonAt scope context tailReturns (id :: rest) resultType
        (Core.LocalControl.sequence resultType
          (Core.LocalControl.conditional resultType conditionCode thenCode elseCode) body)

theorem Tree.heapEffects
    {source : TypedSource} {reasonAt : ExpressionId → Core.Word} {scope : SourceCoreLocalCell.Scope}
    {context : Context} {tailReturns : Bool} {statements : List StatementId} {type : Core.Ty} {code : Core.Expr}
    (tree : Tree source reasonAt scope context tailReturns statements type code) : Core.HeapEffects.Expression code := by
  induction tree with
  | nil => exact .inRight (.inLeft .unit)
  | returnUnit => exact .inRight (.inRight .unit)
  | returnValue _ _ _ value | tailExpression _ _ value =>
      exact .caseE (.of_readOnly (GeneralExpressions.Control.readOnly value)) (.inLeft .var)
        (.inRight (.inRight .var))
  | letUninitialized _ _ _ _ _ tail => exact .letE (.newCell (.inLeft .unit)) tail
  | letInitialized _ _ _ _ value _ tail =>
      exact .caseE (.of_readOnly (GeneralExpressions.Control.readOnly value)) (.inLeft .var)
        (.letE (.newCell (.inRight .var)) (tail.weakenAt 1))
  | assign _ _ _ value _ tail =>
      exact .letE .var
        (.caseE ((Core.HeapEffects.Expression.of_readOnly (GeneralExpressions.Control.readOnly value)).weakenAt 0)
          (.inLeft .var) (.letE (.storeCell .var (.inRight .var)) (((tail.weakenAt 0).weakenAt 0).weakenAt 0)))
  | discard _ _ _ _ value _ tail =>
      exact .caseE (.of_readOnly (GeneralExpressions.Control.readOnly value)) (.inLeft .var) (tail.weakenAt 0)
  | block _ _ _ _ block tail =>
      exact .caseE block (.inLeft .var)
        (.caseE .var ((tail.weakenAt 0).weakenAt 0) (.inRight (.inRight .var)))
  | ifThen _ _ condition _ _ _ thenTree elseTree tail =>
      exact .caseE
        (.caseE (.of_readOnly (GeneralExpressions.Control.readOnly condition)) (.inLeft .var)
          (.ifE .var (thenTree.weakenAt 0) (elseTree.weakenAt 0))) (.inLeft .var)
        (.caseE .var ((tail.weakenAt 0).weakenAt 0) (.inRight (.inRight .var)))

theorem Tree.hasType
    {source : TypedSource} {reasonAt : ExpressionId → Core.Word} {scope : SourceCoreLocalCell.Scope}
    {context : Context} {tailReturns : Bool} {statements : List StatementId} {type : Core.Ty} {code : Core.Expr}
    (tree : Tree source reasonAt scope context tailReturns statements type code)
    (wellFormed : Core.Ty.WellFormed [] type) :
    Core.HasType (SourceCoreLocalCell.coreContext scope) code (Core.LocalControl.resultType type) := by
  induction tree with
  | nil => exact Core.LocalControl.fallthrough_hasType wellFormed
  | returnUnit => exact Core.LocalControl.returned_hasType .unit
  | returnValue _ _ _ value | tailExpression _ _ value =>
      exact Core.LocalControl.returnValue_hasType wellFormed value.hasType
  | letUninitialized _ _ binding _ _ tail =>
      exact Core.LocalSequence.letUninitialized_hasType (binding.types.wellFormed []) (tail wellFormed)
  | letInitialized _ _ _ _ value _ tail =>
      exact Core.LocalSequence.letInitialized_hasType (.sum .unit wellFormed) value.hasType (tail wellFormed)
  | assign _ _ target value _ tail =>
      exact Core.LocalSequence.assign_hasType (.sum .unit wellFormed)
        (.var (SourceCoreLocalCell.lookup?_context target.slot)) value.hasType (tail wellFormed)
  | discard _ _ _ _ value _ tail =>
      exact Core.LocalSequence.discard_hasType (.sum .unit wellFormed) value.hasType (tail wellFormed)
  | block _ _ _ _ block tail => exact Core.LocalControl.sequence_hasType wellFormed (block wellFormed) (tail wellFormed)
  | ifThen _ _ condition _ _ _ thenTree elseTree tail =>
      exact Core.LocalControl.sequence_hasType wellFormed
        (Core.LocalControl.conditional_hasType wellFormed condition.hasType (thenTree wellFormed) (elseTree wellFormed))
        (tail wellFormed)

end Solcore.SourceSemantics.CoreLowering.ControlStatements
