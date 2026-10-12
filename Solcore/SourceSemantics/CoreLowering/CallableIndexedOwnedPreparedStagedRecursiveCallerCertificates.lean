import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedReadProductTreeBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRecursiveCallerSourceReceipts
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionTupleCertificates
import Solcore.SourceSemantics.CoreLowering.RecursiveStageTupleMeaning
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConditionalCertificates
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConstructorExtraction
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionIndexExtraction
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDirectCallCertificates
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBuiltinCallCertificates

/-! Successful compilation constructs a finite recursive caller certificate.
The callee and ordered argument vector retain the exact compiler occurrences,
including repetitions. Raw Source typing precedes recursive extraction. These
are static receipts: runtime states, execution laws and called-body meaning are
not certificate fields. Reachable call authority is indexed by the actual tree.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates
open Core Frontend SourceInference
open CallableIndexedOwnedIndirectSourceAdapters (SourceParent)

inductive Syntax (source : TypedSource) : ExpressionId → Prop where
  | leaf {id} (tree : CompatibleExpressionProducts.Syntax source id) : Syntax source id
  | group {id node inner} (found : source.lookupExpression? id = some node)
      (form : node.form = .group inner) (child : Syntax source inner) : Syntax source id
  | tuple {id node ids} (found : source.lookupExpression? id = some node)
      (form : node.form = .tuple ids)
      (children : ∀ child, child ∈ ids → Syntax source child) : Syntax source id
  | constructor {id node instantiation ids} (found : source.lookupExpression? id = some node)
      (form : node.form = .constructor instantiation ids)
      (ranges : CompatibleSourceInstantiationClosure.ClosedParameterRange instantiation.parameterSubstitution)
      (children : ∀ child, child ∈ ids → Syntax source child) : Syntax source id
  | call {id node callee ids metadata} (found : source.lookupExpression? id = some node)
      (form : node.form = .call callee ids (.indirect metadata))
      (calleeSyntax : Syntax source callee)
      (children : ∀ child, child ∈ ids → Syntax source child) : Syntax source id
  | unary {id node operator operand} (found : source.lookupExpression? id = some node)
      (form : node.form = .unary operator operand) (child : Syntax source operand) : Syntax source id
  | binary {id node left operator right} (found : source.lookupExpression? id = some node)
      (form : node.form = .binary left operator right)
      (first : Syntax source left) (second : Syntax source right) : Syntax source id
  | conditional {id node condition yes no} (found : source.lookupExpression? id = some node)
      (form : node.form = .conditional condition yes no)
      (test : Syntax source condition) (thenBranch : Syntax source yes) (elseBranch : Syntax source no) : Syntax source id

structure PolicyFor (policy : SourceCoreFunctions.Policy) (compilation : SourceCoreFunctions.Context)
    (readFuel : Nat) (values : SourceCoreCompatibleValues.Context) (source : TypedSource)
    (scope : SourceCoreLocalCell.Scope) (reasonAt : ExpressionId → Word) : Prop where
  special : ∀ id, Syntax source id → ∀ child budget, (match policy.lowerSpecial? with
    | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
    | some lower => lower compilation child budget source scope id reasonAt) = .ok none
  read : ∀ id, Syntax source id → policy.readExpression source id =
    SourceCoreCompatibleDataExpressions.readExpression values.checked source id
  lower : policy.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values
  leaf : policy.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values

/-- Only occurrences admitted by the enclosing body need policy facts. -/
structure PolicyOn (policy : SourceCoreFunctions.Policy) (compilation : SourceCoreFunctions.Context)
    (readFuel : Nat) (values : SourceCoreCompatibleValues.Context) (source : TypedSource)
    (scope : SourceCoreLocalCell.Scope) (reasonAt : ExpressionId → Word)
    (allowed : ExpressionId → Prop) : Prop where
  special : ∀ id, allowed id → Syntax source id → ∀ child budget, (match policy.lowerSpecial? with
    | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
    | some lower => lower compilation child budget source scope id reasonAt) = .ok none
  read : ∀ id, allowed id → Syntax source id → policy.readExpression source id =
    SourceCoreCompatibleDataExpressions.readExpression values.checked source id
  lower : policy.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values
  leaf : policy.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values

theorem PolicyFor.on {policy : SourceCoreFunctions.Policy} {compilation : SourceCoreFunctions.Context}
    {readFuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}
    (profile : PolicyFor policy compilation readFuel values source scope reasonAt)
    (allowed : ExpressionId → Prop) : PolicyOn policy compilation readFuel values source scope reasonAt allowed :=
  ⟨fun id _ tree => profile.special id tree, fun id _ tree => profile.read id tree, profile.lower, profile.leaf⟩

inductive GeneralSyntax (source : TypedSource) : ExpressionId → Prop where
  | leaf {id} (tree : CompatibleExpressionProducts.Syntax source id) : GeneralSyntax source id
  | group {id node inner} (found : source.lookupExpression? id = some node)
      (form : node.form = .group inner) (child : GeneralSyntax source inner) : GeneralSyntax source id
  | tuple {id node ids} (found : source.lookupExpression? id = some node)
      (form : node.form = .tuple ids)
      (children : ∀ child, child ∈ ids → GeneralSyntax source child) : GeneralSyntax source id
  | constructor {id node instantiation ids} (found : source.lookupExpression? id = some node)
      (form : node.form = .constructor instantiation ids)
      (ranges : CompatibleSourceInstantiationClosure.ClosedParameterRange instantiation.parameterSubstitution)
      (children : ∀ child, child ∈ ids → GeneralSyntax source child) : GeneralSyntax source id
  | builtin {id node callee ids function} (found : source.lookupExpression? id = some node)
      (form : node.form = .call callee ids (.builtinFunction function))
      (children : ∀ child, child ∈ ids → GeneralSyntax source child) : GeneralSyntax source id
  | direct {id node callee ids instantiation}
      (found : source.lookupExpression? id = some node)
      (form : node.form = .call callee ids (.declaration instantiation))
      (monomorphic : CallableIndexedOwnedPreparedStagedDirectCallCertificates.Monomorphic instantiation)
      (children : ∀ child, child ∈ ids → GeneralSyntax source child) : GeneralSyntax source id
  | call {id node callee ids metadata} (found : source.lookupExpression? id = some node)
      (form : node.form = .call callee ids (.indirect metadata))
      (calleeSyntax : GeneralSyntax source callee)
      (children : ∀ child, child ∈ ids → GeneralSyntax source child) : GeneralSyntax source id
  | unary {id node operator operand} (found : source.lookupExpression? id = some node)
      (form : node.form = .unary operator operand) (child : GeneralSyntax source operand) : GeneralSyntax source id
  | binary {id node left operator right} (found : source.lookupExpression? id = some node)
      (form : node.form = .binary left operator right)
      (first : GeneralSyntax source left) (second : GeneralSyntax source right) : GeneralSyntax source id
  | conditional {id node condition yes no} (found : source.lookupExpression? id = some node)
      (form : node.form = .conditional condition yes no)
      (test : GeneralSyntax source condition) (thenBranch : GeneralSyntax source yes) (elseBranch : GeneralSyntax source no) : GeneralSyntax source id

  | index {id node base key keyNode} (found : source.lookupExpression? id = some node)
      (form : node.form = .index base key) (keyFound : source.lookupExpression? key = some keyNode)
      (scalar : CompatibleExpressionIndices.SourceScalar keyNode.type)
      (first : GeneralSyntax source base) (second : GeneralSyntax source key) : GeneralSyntax source id

structure GeneralPolicyFor (policy : SourceCoreFunctions.Policy) (compilation : SourceCoreFunctions.Context)
    (readFuel : Nat) (values : SourceCoreCompatibleValues.Context) (source : TypedSource)
    (scope : SourceCoreLocalCell.Scope) (reasonAt : ExpressionId → Word) : Prop where
  special : ∀ id, GeneralSyntax source id → ∀ child budget, (match policy.lowerSpecial? with
    | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
    | some lower => lower compilation child budget source scope id reasonAt) = .ok none
  read : ∀ id, GeneralSyntax source id → policy.readExpression source id =
    SourceCoreCompatibleDataExpressions.readExpression values.checked source id
  lower : policy.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values
  leaf : policy.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values

/-- Only occurrences admitted by the enclosing body need policy facts. -/
structure GeneralPolicyOn (policy : SourceCoreFunctions.Policy) (compilation : SourceCoreFunctions.Context)
    (readFuel : Nat) (values : SourceCoreCompatibleValues.Context) (source : TypedSource)
    (scope : SourceCoreLocalCell.Scope) (reasonAt : ExpressionId → Word)
    (allowed : ExpressionId → Prop) : Prop where
  special : ∀ id, allowed id → GeneralSyntax source id → ∀ child budget, (match policy.lowerSpecial? with
    | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
    | some lower => lower compilation child budget source scope id reasonAt) = .ok none
  read : ∀ id, allowed id → GeneralSyntax source id → policy.readExpression source id =
    SourceCoreCompatibleDataExpressions.readExpression values.checked source id
  lower : policy.lowerRead = SourceCoreCompatibleDataExpressions.lowerRead readFuel values
  leaf : policy.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values

theorem GeneralPolicyFor.on {policy : SourceCoreFunctions.Policy} {compilation : SourceCoreFunctions.Context}
    {readFuel : Nat} {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}
    (profile : GeneralPolicyFor policy compilation readFuel values source scope reasonAt)
    (allowed : ExpressionId → Prop) : GeneralPolicyOn policy compilation readFuel values source scope reasonAt allowed :=
  ⟨fun id _ tree => profile.special id tree, fun id _ tree => profile.read id tree, profile.lower, profile.leaf⟩

inductive Certificate (policy : SourceCoreFunctions.Policy) (body : SourceCoreFunctions.BodyLowerer)
    (compilation : SourceCoreFunctions.Context) (readFuel : Nat)
    (values : SourceCoreCompatibleValues.Context) (source : TypedSource)
    (context : SourceSemantics.Context) (reasonAt : ExpressionId → Word)
    (scope : SourceCoreLocalCell.Scope) : ExpressionId → SourceCoreBasic.LoweredExpr → Prop where
  | leaf {id code}
      (tree : CallableIndexedOwnedPreparedStagedReadProductTreeBounds.Certificate readFuel values
        source context compilation.solvedRequirements reasonAt scope id code) :
      Certificate policy body compilation readFuel values source context reasonAt scope id code
  | group {id node inner innerNode code}
      (metadata : CompatibleExpressionPrimitives.Metadata values.checked source id node code.type)
      (form : node.form = .group inner)
      (innerFound : source.lookupExpression? inner = some innerNode)
      (sourceType : node.type = innerNode.type)
      (child : Certificate policy body compilation readFuel values source context reasonAt scope inner code) :
      Certificate policy body compilation readFuel values source context reasonAt scope id code
  | tuple {id node ids types codes}
      (header : CompatibleExpressionTuples.Header values source id node ids types codes)
      (sequence : DataExpressionSequence.Tree source
        (RecursiveStageTupleMeaning.Entries scope (ids.zip codes)) scope ids types codes)
      (children : ∀ child code, (child, code) ∈ ids.zip codes →
        Certificate policy body compilation readFuel values source context reasonAt scope child code) :
      Certificate policy body compilation readFuel values source context reasonAt scope id
        (SourceCoreCalls.packArguments codes)
  | constructor {id node instantiation ids tag headerWord codes}
      (header : CompatibleExpressionConstructors.Header values source id node instantiation tag headerWord codes)
      (form : node.form = .constructor instantiation ids)
      (admissible : SourceSemantics.DataConstructorInstantiation.Admissible context instantiation)
      (ranges : CompatibleSourceInstantiationClosure.ClosedParameterRange instantiation.parameterSubstitution)
      (count : ids.length = instantiation.payloadTypes.length)
      (nodes : CompatibleExpressionConstructors.Nodes source ids instantiation.payloadTypes codes)
      (sequence : DataExpressionSequence.Tree source
        (RecursiveStageTupleMeaning.Entries scope (ids.zip codes)) scope ids instantiation.payloadTypes codes)
      (children : ∀ child code, (child, code) ∈ ids.zip codes →
        Certificate policy body compilation readFuel values source context reasonAt scope child code) :
      Certificate policy body compilation readFuel values source context reasonAt scope id
        ⟨.namedData tag.owner, SourceCoreCompatibleDataExpressions.construct tag headerWord
          (SourceCoreCalls.packArguments codes).expression⟩
  | builtin {id callee ids function fuel lowered}
      (compiler : CallableIndexedOwnedPreparedStagedBuiltinCallCertificates.Receipt policy body fuel compilation
        values source scope id callee ids function reasonAt lowered)
      (calleeTyped : DirectBuiltinCalleeValid source callee function)
      (sourceType : compiler.node.type = function.returnType)
      (nativeTypes : compiler.codes.map (·.type) = CompatibleBuiltinMeaning.argumentTypes function)
      (sequence : DataExpressionSequence.Tree source
        (RecursiveStageTupleMeaning.Entries scope (ids.zip compiler.codes)) scope ids function.parameterTypes compiler.codes)
      (children : ∀ child code, (child, code) ∈ ids.zip compiler.codes →
        Certificate policy body compilation readFuel values source context reasonAt scope child code) :
      Certificate policy body compilation readFuel values source context reasonAt scope id lowered
  | direct {id callee ids instantiation fuel lowered types}
      (compiler : CallableIndexedOwnedPreparedStagedDirectCallCertificates.Receipt policy body fuel compilation
        values source scope id callee ids instantiation reasonAt lowered)
      (calleeTyped : DirectDeclarationCalleeValid context source callee instantiation)
      (application : DeclarationApplicationValid context instantiation types compiler.node.type instantiation.predicates)
      (sequence : DataExpressionSequence.Tree source
        (RecursiveStageTupleMeaning.Entries scope (ids.zip compiler.codes)) scope ids types compiler.codes)
      (children : ∀ child code, (child, code) ∈ ids.zip compiler.codes →
        Certificate policy body compilation readFuel values source context reasonAt scope child code) :
      Certificate policy body compilation readFuel values source context reasonAt scope id lowered
  | call {id callee ids metadata fuel lowered types}
      (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
        id callee ids metadata reasonAt lowered)
      (sequence : DataExpressionSequence.Tree source
        (RecursiveStageTupleMeaning.Entries scope compiler.entries) scope ids types compiler.codes)
      (children : ∀ child code, (child, code) ∈ compiler.entries →
        Certificate policy body compilation readFuel values source context reasonAt scope child code) :
      Certificate policy body compilation readFuel values source context reasonAt scope id lowered

  | unary {id node operand childNode operator operandType resultType core childCode}
      (metadata : CompatibleExpressionPrimitives.Metadata values.checked source id node core.resultType)
      (form : node.form = .unary operator operand)
      (found : source.lookupExpression? operand = some childNode)
      (inputType : childNode.type = operandType) (outputType : node.type = resultType)
      (profile : CompatibleExpressionPrimitives.UnaryProfile operator operandType resultType core)
      (child : Certificate policy body compilation readFuel values source context reasonAt scope operand ⟨core.operandType, childCode⟩) :
      Certificate policy body compilation readFuel values source context reasonAt scope id
        ⟨core.resultType, LocalPrimitiveResults.unary core childCode⟩
  | binary {id node left right leftNode rightNode operator operandType resultType mode leftCode rightCode}
      (metadata : CompatibleExpressionPrimitives.Metadata values.checked source id node (mode.resultType operator))
      (form : node.form = .binary left operator right)
      (leftFound : source.lookupExpression? left = some leftNode)
      (rightFound : source.lookupExpression? right = some rightNode)
      (leftType : leftNode.type = operandType) (rightType : rightNode.type = operandType)
      (outputType : node.type = resultType)
      (profile : CompatibleExpressionPrimitives.BinaryProfile operator operandType resultType mode)
      (first : Certificate policy body compilation readFuel values source context reasonAt scope left ⟨mode.operandType operator, leftCode⟩)
      (second : Certificate policy body compilation readFuel values source context reasonAt scope right ⟨mode.operandType operator, rightCode⟩) :
      Certificate policy body compilation readFuel values source context reasonAt scope id
        ⟨mode.resultType operator, mode.binary operator leftCode rightCode⟩

  | conditional {id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode}
      (metadata : CompatibleExpressionPrimitives.Metadata values.checked source id node type)
      (form : node.form = .conditional condition thenId elseId)
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (thenFound : source.lookupExpression? thenId = some thenNode)
      (elseFound : source.lookupExpression? elseId = some elseNode)
      (conditionType : conditionNode.type = .bool)
      (thenType : thenNode.type = node.type) (elseType : elseNode.type = node.type)
      (conditionTree : Certificate policy body compilation readFuel values source context reasonAt scope condition ⟨.bool, conditionCode⟩)
      (thenTree : Certificate policy body compilation readFuel values source context reasonAt scope thenId ⟨type, thenCode⟩)
      (elseTree : Certificate policy body compilation readFuel values source context reasonAt scope elseId ⟨type, elseCode⟩) :
      Certificate policy body compilation readFuel values source context reasonAt scope id
        ⟨type, LocalControl.choose type conditionCode thenCode elseCode⟩

  | index {id node base key baseNode keyNode layout comparison first second}
      (header : CompatibleExpressionIndices.Header values source id base node baseNode layout comparison first second)
      (keyFound : source.lookupExpression? key = some keyNode)
      (form : node.form = .index base key)
      (sourceType : baseNode.type = .mapping keyNode.type node.type)
      (scalar : CompatibleExpressionIndices.SourceScalar keyNode.type)
      (firstTree : Certificate policy body compilation readFuel values source context reasonAt scope base first)
      (secondTree : Certificate policy body compilation readFuel values source context reasonAt scope key second) :
      Certificate policy body compilation readFuel values source context reasonAt scope id
        ⟨layout.valueType, SourceCoreCompatibleDataExpressions.index layout comparison.expression
          first.expression second.expression (reasonAt id)⟩

variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
  {compilation : SourceCoreFunctions.Context} {readFuel : Nat}
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {reasonAt : ExpressionId → Word}

/-- A call is reachable only through this exact static certificate. Authority
for unrelated accepted receipts is not needed. The argument path retains the
literal membership proof, including the leading callee and repeated entries. -/
inductive Calls {fuel : Nat} {callScope : SourceCoreLocalCell.Scope}
    {callId callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
    {lowered : SourceCoreBasic.LoweredExpr}
    (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source callScope
      callId callee ids metadata reasonAt lowered) :
    {scope : SourceCoreLocalCell.Scope} → {id : ExpressionId} → {code : SourceCoreBasic.LoweredExpr} →
      Certificate policy body compilation readFuel values source context reasonAt scope id code → Prop where
  | here {types}
      (sequence : DataExpressionSequence.Tree source
        (RecursiveStageTupleMeaning.Entries callScope compiler.entries) callScope ids types compiler.codes)
      (children : ∀ child code, (child, code) ∈ compiler.entries →
        Certificate policy body compilation readFuel values source context reasonAt callScope child code) :
      Calls compiler (.call compiler sequence children)
  | group {scope id node inner innerNode code}
      {actual : CompatibleExpressionPrimitives.Metadata values.checked source id node code.type}
      {form : node.form = .group inner} {found : source.lookupExpression? inner = some innerNode}
      {type : node.type = innerNode.type}
      {child : Certificate policy body compilation readFuel values source context reasonAt scope inner code}
      (inside : Calls compiler child) : Calls compiler (.group actual form found type child)
  | tuple_child {scope id node tupleIds types codes}
      {header : CompatibleExpressionTuples.Header values source id node tupleIds types codes}
      {sequence : DataExpressionSequence.Tree source
        (RecursiveStageTupleMeaning.Entries scope (tupleIds.zip codes)) scope tupleIds types codes}
      {children : ∀ child code, (child, code) ∈ tupleIds.zip codes →
        Certificate policy body compilation readFuel values source context reasonAt scope child code}
      {child childCode} (member : (child, childCode) ∈ tupleIds.zip codes)
      (inside : Calls compiler (children child childCode member)) :
      Calls compiler (.tuple header sequence children)
  | constructor_child {scope id node instantiation constructorIds tag headerWord codes}
      {header : CompatibleExpressionConstructors.Header values source id node instantiation tag headerWord codes}
      {form : node.form = .constructor instantiation constructorIds}
      {admissible : SourceSemantics.DataConstructorInstantiation.Admissible context instantiation}
      {ranges : CompatibleSourceInstantiationClosure.ClosedParameterRange instantiation.parameterSubstitution}
      {count : constructorIds.length = instantiation.payloadTypes.length}
      {nodes : CompatibleExpressionConstructors.Nodes source constructorIds instantiation.payloadTypes codes}
      {sequence : DataExpressionSequence.Tree source
        (RecursiveStageTupleMeaning.Entries scope (constructorIds.zip codes)) scope constructorIds instantiation.payloadTypes codes}
      {children : ∀ child code, (child, code) ∈ constructorIds.zip codes →
        Certificate policy body compilation readFuel values source context reasonAt scope child code}
      {child childCode} (member : (child, childCode) ∈ constructorIds.zip codes)
      (inside : Calls compiler (children child childCode member)) :
      Calls compiler (.constructor header form admissible ranges count nodes sequence children)
  | builtin_child {scope id otherCallee otherIds function otherFuel code}
      {outer : CallableIndexedOwnedPreparedStagedBuiltinCallCertificates.Receipt policy body otherFuel compilation
        values source scope id otherCallee otherIds function reasonAt code}
      {calleeTyped : DirectBuiltinCalleeValid source otherCallee function}
      {sourceType : outer.node.type = function.returnType}
      {nativeTypes : outer.codes.map (·.type) = CompatibleBuiltinMeaning.argumentTypes function}
      {sequence : DataExpressionSequence.Tree source
        (RecursiveStageTupleMeaning.Entries scope (otherIds.zip outer.codes)) scope otherIds function.parameterTypes outer.codes}
      {children : ∀ child childCode, (child, childCode) ∈ otherIds.zip outer.codes →
        Certificate policy body compilation readFuel values source context reasonAt scope child childCode}
      {child childCode} (member : (child, childCode) ∈ otherIds.zip outer.codes)
      (inside : Calls compiler (children child childCode member)) :
      Calls compiler (.builtin outer calleeTyped sourceType nativeTypes sequence children)
  | direct_child {scope id otherCallee otherIds instantiation otherFuel code types}
      {outer : CallableIndexedOwnedPreparedStagedDirectCallCertificates.Receipt policy body otherFuel compilation
        values source scope id otherCallee otherIds instantiation reasonAt code}
      {calleeTyped : DirectDeclarationCalleeValid context source otherCallee instantiation}
      {application : DeclarationApplicationValid context instantiation types outer.node.type instantiation.predicates}
      {sequence : DataExpressionSequence.Tree source
        (RecursiveStageTupleMeaning.Entries scope (otherIds.zip outer.codes)) scope otherIds types outer.codes}
      {children : ∀ child childCode, (child, childCode) ∈ otherIds.zip outer.codes →
        Certificate policy body compilation readFuel values source context reasonAt scope child childCode}
      {child childCode} (member : (child, childCode) ∈ otherIds.zip outer.codes)
      (inside : Calls compiler (children child childCode member)) :
      Calls compiler (.direct outer calleeTyped application sequence children)
  | call_child {scope id otherCallee otherIds otherMetadata otherFuel code types}
      {outer : CallableIndirectCallCertificates.Receipt policy body otherFuel compilation source scope
        id otherCallee otherIds otherMetadata reasonAt code}
      {sequence : DataExpressionSequence.Tree source
        (RecursiveStageTupleMeaning.Entries scope outer.entries) scope otherIds types outer.codes}
      {children : ∀ child childCode, (child, childCode) ∈ outer.entries →
        Certificate policy body compilation readFuel values source context reasonAt scope child childCode}
      {child childCode} (member : (child, childCode) ∈ outer.entries)
      (inside : Calls compiler (children child childCode member)) :
      Calls compiler (.call outer sequence children)

  | unary_child {scope id node operand childNode operator operandType resultType core childCode}
      {actual : CompatibleExpressionPrimitives.Metadata values.checked source id node core.resultType}
      {form : node.form = .unary operator operand} {found : source.lookupExpression? operand = some childNode}
      {inputType : childNode.type = operandType} {outputType : node.type = resultType}
      {profile : CompatibleExpressionPrimitives.UnaryProfile operator operandType resultType core}
      {child : Certificate policy body compilation readFuel values source context reasonAt scope operand ⟨core.operandType, childCode⟩}
      (inside : Calls compiler child) :
      Calls compiler (.unary actual form found inputType outputType profile child)
  | binary_left {scope id node left right leftNode rightNode operator operandType resultType mode leftCode rightCode}
      {actual : CompatibleExpressionPrimitives.Metadata values.checked source id node (mode.resultType operator)}
      {form : node.form = .binary left operator right}
      {leftFound : source.lookupExpression? left = some leftNode} {rightFound : source.lookupExpression? right = some rightNode}
      {leftType : leftNode.type = operandType} {rightType : rightNode.type = operandType} {outputType : node.type = resultType}
      {profile : CompatibleExpressionPrimitives.BinaryProfile operator operandType resultType mode}
      {first : Certificate policy body compilation readFuel values source context reasonAt scope left ⟨mode.operandType operator, leftCode⟩}
      {second : Certificate policy body compilation readFuel values source context reasonAt scope right ⟨mode.operandType operator, rightCode⟩}
      (inside : Calls compiler first) :
      Calls compiler (.binary actual form leftFound rightFound leftType rightType outputType profile first second)
  | binary_right {scope id node left right leftNode rightNode operator operandType resultType mode leftCode rightCode}
      {actual : CompatibleExpressionPrimitives.Metadata values.checked source id node (mode.resultType operator)}
      {form : node.form = .binary left operator right}
      {leftFound : source.lookupExpression? left = some leftNode} {rightFound : source.lookupExpression? right = some rightNode}
      {leftType : leftNode.type = operandType} {rightType : rightNode.type = operandType} {outputType : node.type = resultType}
      {profile : CompatibleExpressionPrimitives.BinaryProfile operator operandType resultType mode}
      {first : Certificate policy body compilation readFuel values source context reasonAt scope left ⟨mode.operandType operator, leftCode⟩}
      {second : Certificate policy body compilation readFuel values source context reasonAt scope right ⟨mode.operandType operator, rightCode⟩}
      (inside : Calls compiler second) :
      Calls compiler (.binary actual form leftFound rightFound leftType rightType outputType profile first second)
  | conditional_condition {scope id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode}
      {actual : CompatibleExpressionPrimitives.Metadata values.checked source id node type}
      {form : node.form = .conditional condition thenId elseId}
      {conditionFound : source.lookupExpression? condition = some conditionNode}
      {thenFound : source.lookupExpression? thenId = some thenNode} {elseFound : source.lookupExpression? elseId = some elseNode}
      {conditionType : conditionNode.type = .bool} {thenType : thenNode.type = node.type} {elseType : elseNode.type = node.type}
      {conditionTree : Certificate policy body compilation readFuel values source context reasonAt scope condition ⟨.bool, conditionCode⟩}
      {thenTree : Certificate policy body compilation readFuel values source context reasonAt scope thenId ⟨type, thenCode⟩} {elseTree : Certificate policy body compilation readFuel values source context reasonAt scope elseId ⟨type, elseCode⟩}
      (inside : Calls compiler conditionTree) :
      Calls compiler (.conditional actual form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree)
  | conditional_then {scope id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode}
      {actual : CompatibleExpressionPrimitives.Metadata values.checked source id node type}
      {form : node.form = .conditional condition thenId elseId}
      {conditionFound : source.lookupExpression? condition = some conditionNode}
      {thenFound : source.lookupExpression? thenId = some thenNode} {elseFound : source.lookupExpression? elseId = some elseNode}
      {conditionType : conditionNode.type = .bool} {thenType : thenNode.type = node.type} {elseType : elseNode.type = node.type}
      {conditionTree : Certificate policy body compilation readFuel values source context reasonAt scope condition ⟨.bool, conditionCode⟩}
      {thenTree : Certificate policy body compilation readFuel values source context reasonAt scope thenId ⟨type, thenCode⟩} {elseTree : Certificate policy body compilation readFuel values source context reasonAt scope elseId ⟨type, elseCode⟩}
      (inside : Calls compiler thenTree) :
      Calls compiler (.conditional actual form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree)
  | conditional_else {scope id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode}
      {actual : CompatibleExpressionPrimitives.Metadata values.checked source id node type}
      {form : node.form = .conditional condition thenId elseId}
      {conditionFound : source.lookupExpression? condition = some conditionNode}
      {thenFound : source.lookupExpression? thenId = some thenNode} {elseFound : source.lookupExpression? elseId = some elseNode}
      {conditionType : conditionNode.type = .bool} {thenType : thenNode.type = node.type} {elseType : elseNode.type = node.type}
      {conditionTree : Certificate policy body compilation readFuel values source context reasonAt scope condition ⟨.bool, conditionCode⟩}
      {thenTree : Certificate policy body compilation readFuel values source context reasonAt scope thenId ⟨type, thenCode⟩} {elseTree : Certificate policy body compilation readFuel values source context reasonAt scope elseId ⟨type, elseCode⟩}
      (inside : Calls compiler elseTree) :
      Calls compiler (.conditional actual form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree)

  | index_base {scope id node base key baseNode keyNode layout comparison first second}
      {header : CompatibleExpressionIndices.Header values source id base node baseNode layout comparison first second}
      {keyFound : source.lookupExpression? key = some keyNode}
      {form : node.form = .index base key}
      {sourceType : baseNode.type = .mapping keyNode.type node.type}
      {scalar : CompatibleExpressionIndices.SourceScalar keyNode.type}
      {firstTree : Certificate policy body compilation readFuel values source context reasonAt scope base first}
      {secondTree : Certificate policy body compilation readFuel values source context reasonAt scope key second}
      (inside : Calls compiler firstTree) :
      Calls compiler (.index header keyFound form sourceType scalar firstTree secondTree)
  | index_key {scope id node base key baseNode keyNode layout comparison first second}
      {header : CompatibleExpressionIndices.Header values source id base node baseNode layout comparison first second}
      {keyFound : source.lookupExpression? key = some keyNode}
      {form : node.form = .index base key}
      {sourceType : baseNode.type = .mapping keyNode.type node.type}
      {scalar : CompatibleExpressionIndices.SourceScalar keyNode.type}
      {firstTree : Certificate policy body compilation readFuel values source context reasonAt scope base first}
      {secondTree : Certificate policy body compilation readFuel values source context reasonAt scope key second}
      (inside : Calls compiler secondTree) :
      Calls compiler (.index header keyFound form sourceType scalar firstTree secondTree)

/-- Reachability of a direct call follows only actual recursive argument certificates. -/
inductive DirectCalls {fuel : Nat} {callScope : SourceCoreLocalCell.Scope}
    {callId callee : ExpressionId} {ids : List ExpressionId} {instantiation : DeclarationInstantiation}
    {lowered : SourceCoreBasic.LoweredExpr}
    (compiler : CallableIndexedOwnedPreparedStagedDirectCallCertificates.Receipt policy body fuel compilation
      values source callScope callId callee ids instantiation reasonAt lowered) :
    {scope : SourceCoreLocalCell.Scope} → {id : ExpressionId} → {code : SourceCoreBasic.LoweredExpr} →
      Certificate policy body compilation readFuel values source context reasonAt scope id code → Prop where
  | here {types}
      (calleeTyped : DirectDeclarationCalleeValid context source callee instantiation)
      (application : DeclarationApplicationValid context instantiation types compiler.node.type instantiation.predicates)
      (sequence : DataExpressionSequence.Tree source
        (RecursiveStageTupleMeaning.Entries callScope (ids.zip compiler.codes)) callScope ids types compiler.codes)
      (children : ∀ child code, (child, code) ∈ ids.zip compiler.codes →
        Certificate policy body compilation readFuel values source context reasonAt callScope child code) :
      DirectCalls compiler (.direct compiler calleeTyped application sequence children)
  | group {scope id node inner innerNode code}
      {actual : CompatibleExpressionPrimitives.Metadata values.checked source id node code.type}
      {form : node.form = .group inner} {found : source.lookupExpression? inner = some innerNode}
      {type : node.type = innerNode.type}
      {child : Certificate policy body compilation readFuel values source context reasonAt scope inner code}
      (inside : DirectCalls compiler child) : DirectCalls compiler (.group actual form found type child)
  | tuple_child {scope id node tupleIds types codes}
      {header : CompatibleExpressionTuples.Header values source id node tupleIds types codes}
      {sequence : DataExpressionSequence.Tree source
        (RecursiveStageTupleMeaning.Entries scope (tupleIds.zip codes)) scope tupleIds types codes}
      {children : ∀ child code, (child, code) ∈ tupleIds.zip codes →
        Certificate policy body compilation readFuel values source context reasonAt scope child code}
      {child childCode} (member : (child, childCode) ∈ tupleIds.zip codes)
      (inside : DirectCalls compiler (children child childCode member)) :
      DirectCalls compiler (.tuple header sequence children)
  | constructor_child {scope id node instantiation constructorIds tag headerWord codes}
      {header : CompatibleExpressionConstructors.Header values source id node instantiation tag headerWord codes}
      {form : node.form = .constructor instantiation constructorIds}
      {admissible : SourceSemantics.DataConstructorInstantiation.Admissible context instantiation}
      {ranges : CompatibleSourceInstantiationClosure.ClosedParameterRange instantiation.parameterSubstitution}
      {count : constructorIds.length = instantiation.payloadTypes.length}
      {nodes : CompatibleExpressionConstructors.Nodes source constructorIds instantiation.payloadTypes codes}
      {sequence : DataExpressionSequence.Tree source
        (RecursiveStageTupleMeaning.Entries scope (constructorIds.zip codes)) scope constructorIds instantiation.payloadTypes codes}
      {children : ∀ child code, (child, code) ∈ constructorIds.zip codes →
        Certificate policy body compilation readFuel values source context reasonAt scope child code}
      {child childCode} (member : (child, childCode) ∈ constructorIds.zip codes)
      (inside : DirectCalls compiler (children child childCode member)) :
      DirectCalls compiler (.constructor header form admissible ranges count nodes sequence children)
  | builtin_child {scope id otherCallee otherIds function otherFuel code}
      {outer : CallableIndexedOwnedPreparedStagedBuiltinCallCertificates.Receipt policy body otherFuel compilation
        values source scope id otherCallee otherIds function reasonAt code}
      {calleeTyped : DirectBuiltinCalleeValid source otherCallee function}
      {sourceType : outer.node.type = function.returnType}
      {nativeTypes : outer.codes.map (·.type) = CompatibleBuiltinMeaning.argumentTypes function}
      {sequence : DataExpressionSequence.Tree source
        (RecursiveStageTupleMeaning.Entries scope (otherIds.zip outer.codes)) scope otherIds function.parameterTypes outer.codes}
      {children : ∀ child childCode, (child, childCode) ∈ otherIds.zip outer.codes →
        Certificate policy body compilation readFuel values source context reasonAt scope child childCode}
      {child childCode} (member : (child, childCode) ∈ otherIds.zip outer.codes)
      (inside : DirectCalls compiler (children child childCode member)) :
      DirectCalls compiler (.builtin outer calleeTyped sourceType nativeTypes sequence children)
  | direct_child {scope id otherCallee otherIds instantiation otherFuel code types}
      {outer : CallableIndexedOwnedPreparedStagedDirectCallCertificates.Receipt policy body otherFuel compilation
        values source scope id otherCallee otherIds instantiation reasonAt code}
      {calleeTyped : DirectDeclarationCalleeValid context source otherCallee instantiation}
      {application : DeclarationApplicationValid context instantiation types outer.node.type instantiation.predicates}
      {sequence : DataExpressionSequence.Tree source
        (RecursiveStageTupleMeaning.Entries scope (otherIds.zip outer.codes)) scope otherIds types outer.codes}
      {children : ∀ child childCode, (child, childCode) ∈ otherIds.zip outer.codes →
        Certificate policy body compilation readFuel values source context reasonAt scope child childCode}
      {child childCode} (member : (child, childCode) ∈ otherIds.zip outer.codes)
      (inside : DirectCalls compiler (children child childCode member)) :
      DirectCalls compiler (.direct outer calleeTyped application sequence children)
  | call_child {scope id otherCallee otherIds otherMetadata otherFuel code types}
      {outer : CallableIndirectCallCertificates.Receipt policy body otherFuel compilation source scope
        id otherCallee otherIds otherMetadata reasonAt code}
      {sequence : DataExpressionSequence.Tree source
        (RecursiveStageTupleMeaning.Entries scope outer.entries) scope otherIds types outer.codes}
      {children : ∀ child childCode, (child, childCode) ∈ outer.entries →
        Certificate policy body compilation readFuel values source context reasonAt scope child childCode}
      {child childCode} (member : (child, childCode) ∈ outer.entries)
      (inside : DirectCalls compiler (children child childCode member)) :
      DirectCalls compiler (.call outer sequence children)

  | unary_child {scope id node operand childNode operator operandType resultType core childCode}
      {actual : CompatibleExpressionPrimitives.Metadata values.checked source id node core.resultType}
      {form : node.form = .unary operator operand} {found : source.lookupExpression? operand = some childNode}
      {inputType : childNode.type = operandType} {outputType : node.type = resultType}
      {profile : CompatibleExpressionPrimitives.UnaryProfile operator operandType resultType core}
      {child : Certificate policy body compilation readFuel values source context reasonAt scope operand ⟨core.operandType, childCode⟩}
      (inside : DirectCalls compiler child) :
      DirectCalls compiler (.unary actual form found inputType outputType profile child)
  | binary_left {scope id node left right leftNode rightNode operator operandType resultType mode leftCode rightCode}
      {actual : CompatibleExpressionPrimitives.Metadata values.checked source id node (mode.resultType operator)}
      {form : node.form = .binary left operator right}
      {leftFound : source.lookupExpression? left = some leftNode} {rightFound : source.lookupExpression? right = some rightNode}
      {leftType : leftNode.type = operandType} {rightType : rightNode.type = operandType} {outputType : node.type = resultType}
      {profile : CompatibleExpressionPrimitives.BinaryProfile operator operandType resultType mode}
      {first : Certificate policy body compilation readFuel values source context reasonAt scope left ⟨mode.operandType operator, leftCode⟩}
      {second : Certificate policy body compilation readFuel values source context reasonAt scope right ⟨mode.operandType operator, rightCode⟩}
      (inside : DirectCalls compiler first) :
      DirectCalls compiler (.binary actual form leftFound rightFound leftType rightType outputType profile first second)
  | binary_right {scope id node left right leftNode rightNode operator operandType resultType mode leftCode rightCode}
      {actual : CompatibleExpressionPrimitives.Metadata values.checked source id node (mode.resultType operator)}
      {form : node.form = .binary left operator right}
      {leftFound : source.lookupExpression? left = some leftNode} {rightFound : source.lookupExpression? right = some rightNode}
      {leftType : leftNode.type = operandType} {rightType : rightNode.type = operandType} {outputType : node.type = resultType}
      {profile : CompatibleExpressionPrimitives.BinaryProfile operator operandType resultType mode}
      {first : Certificate policy body compilation readFuel values source context reasonAt scope left ⟨mode.operandType operator, leftCode⟩}
      {second : Certificate policy body compilation readFuel values source context reasonAt scope right ⟨mode.operandType operator, rightCode⟩}
      (inside : DirectCalls compiler second) :
      DirectCalls compiler (.binary actual form leftFound rightFound leftType rightType outputType profile first second)
  | conditional_condition {scope id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode}
      {actual : CompatibleExpressionPrimitives.Metadata values.checked source id node type}
      {form : node.form = .conditional condition thenId elseId}
      {conditionFound : source.lookupExpression? condition = some conditionNode}
      {thenFound : source.lookupExpression? thenId = some thenNode} {elseFound : source.lookupExpression? elseId = some elseNode}
      {conditionType : conditionNode.type = .bool} {thenType : thenNode.type = node.type} {elseType : elseNode.type = node.type}
      {conditionTree : Certificate policy body compilation readFuel values source context reasonAt scope condition ⟨.bool, conditionCode⟩}
      {thenTree : Certificate policy body compilation readFuel values source context reasonAt scope thenId ⟨type, thenCode⟩} {elseTree : Certificate policy body compilation readFuel values source context reasonAt scope elseId ⟨type, elseCode⟩}
      (inside : DirectCalls compiler conditionTree) :
      DirectCalls compiler (.conditional actual form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree)
  | conditional_then {scope id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode}
      {actual : CompatibleExpressionPrimitives.Metadata values.checked source id node type}
      {form : node.form = .conditional condition thenId elseId}
      {conditionFound : source.lookupExpression? condition = some conditionNode}
      {thenFound : source.lookupExpression? thenId = some thenNode} {elseFound : source.lookupExpression? elseId = some elseNode}
      {conditionType : conditionNode.type = .bool} {thenType : thenNode.type = node.type} {elseType : elseNode.type = node.type}
      {conditionTree : Certificate policy body compilation readFuel values source context reasonAt scope condition ⟨.bool, conditionCode⟩}
      {thenTree : Certificate policy body compilation readFuel values source context reasonAt scope thenId ⟨type, thenCode⟩} {elseTree : Certificate policy body compilation readFuel values source context reasonAt scope elseId ⟨type, elseCode⟩}
      (inside : DirectCalls compiler thenTree) :
      DirectCalls compiler (.conditional actual form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree)
  | conditional_else {scope id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode}
      {actual : CompatibleExpressionPrimitives.Metadata values.checked source id node type}
      {form : node.form = .conditional condition thenId elseId}
      {conditionFound : source.lookupExpression? condition = some conditionNode}
      {thenFound : source.lookupExpression? thenId = some thenNode} {elseFound : source.lookupExpression? elseId = some elseNode}
      {conditionType : conditionNode.type = .bool} {thenType : thenNode.type = node.type} {elseType : elseNode.type = node.type}
      {conditionTree : Certificate policy body compilation readFuel values source context reasonAt scope condition ⟨.bool, conditionCode⟩}
      {thenTree : Certificate policy body compilation readFuel values source context reasonAt scope thenId ⟨type, thenCode⟩} {elseTree : Certificate policy body compilation readFuel values source context reasonAt scope elseId ⟨type, elseCode⟩}
      (inside : DirectCalls compiler elseTree) :
      DirectCalls compiler (.conditional actual form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree)


  | index_base {scope id node base key baseNode keyNode layout comparison first second}
      {header : CompatibleExpressionIndices.Header values source id base node baseNode layout comparison first second}
      {keyFound : source.lookupExpression? key = some keyNode}
      {form : node.form = .index base key}
      {sourceType : baseNode.type = .mapping keyNode.type node.type}
      {scalar : CompatibleExpressionIndices.SourceScalar keyNode.type}
      {firstTree : Certificate policy body compilation readFuel values source context reasonAt scope base first}
      {secondTree : Certificate policy body compilation readFuel values source context reasonAt scope key second}
      (inside : DirectCalls compiler firstTree) :
      DirectCalls compiler (.index header keyFound form sourceType scalar firstTree secondTree)
  | index_key {scope id node base key baseNode keyNode layout comparison first second}
      {header : CompatibleExpressionIndices.Header values source id base node baseNode layout comparison first second}
      {keyFound : source.lookupExpression? key = some keyNode}
      {form : node.form = .index base key}
      {sourceType : baseNode.type = .mapping keyNode.type node.type}
      {scalar : CompatibleExpressionIndices.SourceScalar keyNode.type}
      {firstTree : Certificate policy body compilation readFuel values source context reasonAt scope base first}
      {secondTree : Certificate policy body compilation readFuel values source context reasonAt scope key second}
      (inside : DirectCalls compiler secondTree) :
      DirectCalls compiler (.index header keyFound form sourceType scalar firstTree secondTree)

/-- A legacy pool-only root contains no physically addressed declaration call.
The property follows its finite stored paths, not a runtime or result premise. -/
def NoDirect {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {lowered : SourceCoreBasic.LoweredExpr}
    (root : Certificate policy body compilation readFuel values source context reasonAt scope id lowered) : Prop :=
  ∀ {fuel callScope callId callee ids instantiation callCode}
    (compiler : CallableIndexedOwnedPreparedStagedDirectCallCertificates.Receipt
      policy body fuel compilation values source callScope callId callee ids instantiation reasonAt callCode),
    DirectCalls compiler root → False

/-- A mapping access is retained only along the actual recursive compiler tree. -/
inductive Indexes {indexScope : SourceCoreLocalCell.Scope}
    {indexId base key : ExpressionId} {node baseNode keyNode : ExpressionNode}
    {layout : Core.OrderedMapping.Layout}
    {comparison : SourceCoreCompatibleDataEquality.Prepared values.checked} {indexFirst indexSecond : SourceCoreBasic.LoweredExpr}
    (indexed : CompatibleExpressionIndices.Header values source indexId base node baseNode layout comparison indexFirst indexSecond)
    (indexKeyFound : source.lookupExpression? key = some keyNode)
    (indexForm : node.form = .index base key)
    (indexSourceType : baseNode.type = .mapping keyNode.type node.type)
    (indexScalar : CompatibleExpressionIndices.SourceScalar keyNode.type) :
    {scope : SourceCoreLocalCell.Scope} → {id : ExpressionId} → {code : SourceCoreBasic.LoweredExpr} →
      Certificate policy body compilation readFuel values source context reasonAt scope id code → Prop where
  | here
      (firstTree : Certificate policy body compilation readFuel values source context reasonAt indexScope base indexFirst)
      (secondTree : Certificate policy body compilation readFuel values source context reasonAt indexScope key indexSecond) :
      Indexes (indexScope := indexScope) indexed indexKeyFound indexForm indexSourceType indexScalar
        (.index indexed indexKeyFound indexForm indexSourceType indexScalar firstTree secondTree)
  | group {scope id node inner innerNode code}
      {actual : CompatibleExpressionPrimitives.Metadata values.checked source id node code.type}
      {form : node.form = .group inner} {found : source.lookupExpression? inner = some innerNode}
      {type : node.type = innerNode.type}
      {child : Certificate policy body compilation readFuel values source context reasonAt scope inner code}
      (inside : Indexes (indexScope := indexScope) indexed indexKeyFound indexForm indexSourceType indexScalar child) : Indexes (indexScope := indexScope) indexed indexKeyFound indexForm indexSourceType indexScalar (.group actual form found type child)
  | tuple_child {scope id node tupleIds types codes}
      {header : CompatibleExpressionTuples.Header values source id node tupleIds types codes}
      {sequence : DataExpressionSequence.Tree source
        (RecursiveStageTupleMeaning.Entries scope (tupleIds.zip codes)) scope tupleIds types codes}
      {children : ∀ child code, (child, code) ∈ tupleIds.zip codes →
        Certificate policy body compilation readFuel values source context reasonAt scope child code}
      {child childCode} (member : (child, childCode) ∈ tupleIds.zip codes)
      (inside : Indexes (indexScope := indexScope) indexed indexKeyFound indexForm indexSourceType indexScalar (children child childCode member)) :
      Indexes (indexScope := indexScope) indexed indexKeyFound indexForm indexSourceType indexScalar (.tuple header sequence children)
  | constructor_child {scope id node instantiation constructorIds tag headerWord codes}
      {header : CompatibleExpressionConstructors.Header values source id node instantiation tag headerWord codes}
      {form : node.form = .constructor instantiation constructorIds}
      {admissible : SourceSemantics.DataConstructorInstantiation.Admissible context instantiation}
      {ranges : CompatibleSourceInstantiationClosure.ClosedParameterRange instantiation.parameterSubstitution}
      {count : constructorIds.length = instantiation.payloadTypes.length}
      {nodes : CompatibleExpressionConstructors.Nodes source constructorIds instantiation.payloadTypes codes}
      {sequence : DataExpressionSequence.Tree source
        (RecursiveStageTupleMeaning.Entries scope (constructorIds.zip codes)) scope constructorIds instantiation.payloadTypes codes}
      {children : ∀ child code, (child, code) ∈ constructorIds.zip codes →
        Certificate policy body compilation readFuel values source context reasonAt scope child code}
      {child childCode} (member : (child, childCode) ∈ constructorIds.zip codes)
      (inside : Indexes (indexScope := indexScope) indexed indexKeyFound indexForm indexSourceType indexScalar (children child childCode member)) :
      Indexes (indexScope := indexScope) indexed indexKeyFound indexForm indexSourceType indexScalar (.constructor header form admissible ranges count nodes sequence children)
  | builtin_child {scope id otherCallee otherIds function otherFuel code}
      {outer : CallableIndexedOwnedPreparedStagedBuiltinCallCertificates.Receipt policy body otherFuel compilation
        values source scope id otherCallee otherIds function reasonAt code}
      {calleeTyped : DirectBuiltinCalleeValid source otherCallee function}
      {sourceType : outer.node.type = function.returnType}
      {nativeTypes : outer.codes.map (·.type) = CompatibleBuiltinMeaning.argumentTypes function}
      {sequence : DataExpressionSequence.Tree source
        (RecursiveStageTupleMeaning.Entries scope (otherIds.zip outer.codes)) scope otherIds function.parameterTypes outer.codes}
      {children : ∀ child childCode, (child, childCode) ∈ otherIds.zip outer.codes →
        Certificate policy body compilation readFuel values source context reasonAt scope child childCode}
      {child childCode} (member : (child, childCode) ∈ otherIds.zip outer.codes)
      (inside : Indexes (indexScope := indexScope) indexed indexKeyFound indexForm indexSourceType indexScalar (children child childCode member)) :
      Indexes (indexScope := indexScope) indexed indexKeyFound indexForm indexSourceType indexScalar (.builtin outer calleeTyped sourceType nativeTypes sequence children)
  | direct_child {scope id otherCallee otherIds instantiation otherFuel code types}
      {outer : CallableIndexedOwnedPreparedStagedDirectCallCertificates.Receipt policy body otherFuel compilation
        values source scope id otherCallee otherIds instantiation reasonAt code}
      {calleeTyped : DirectDeclarationCalleeValid context source otherCallee instantiation}
      {application : DeclarationApplicationValid context instantiation types outer.node.type instantiation.predicates}
      {sequence : DataExpressionSequence.Tree source
        (RecursiveStageTupleMeaning.Entries scope (otherIds.zip outer.codes)) scope otherIds types outer.codes}
      {children : ∀ child childCode, (child, childCode) ∈ otherIds.zip outer.codes →
        Certificate policy body compilation readFuel values source context reasonAt scope child childCode}
      {child childCode} (member : (child, childCode) ∈ otherIds.zip outer.codes)
      (inside : Indexes (indexScope := indexScope) indexed indexKeyFound indexForm indexSourceType indexScalar (children child childCode member)) :
      Indexes (indexScope := indexScope) indexed indexKeyFound indexForm indexSourceType indexScalar (.direct outer calleeTyped application sequence children)
  | call_child {scope id otherCallee otherIds otherMetadata otherFuel code types}
      {outer : CallableIndirectCallCertificates.Receipt policy body otherFuel compilation source scope
        id otherCallee otherIds otherMetadata reasonAt code}
      {sequence : DataExpressionSequence.Tree source
        (RecursiveStageTupleMeaning.Entries scope outer.entries) scope otherIds types outer.codes}
      {children : ∀ child childCode, (child, childCode) ∈ outer.entries →
        Certificate policy body compilation readFuel values source context reasonAt scope child childCode}
      {child childCode} (member : (child, childCode) ∈ outer.entries)
      (inside : Indexes (indexScope := indexScope) indexed indexKeyFound indexForm indexSourceType indexScalar (children child childCode member)) :
      Indexes (indexScope := indexScope) indexed indexKeyFound indexForm indexSourceType indexScalar (.call outer sequence children)

  | unary_child {scope id node operand childNode operator operandType resultType core childCode}
      {actual : CompatibleExpressionPrimitives.Metadata values.checked source id node core.resultType}
      {form : node.form = .unary operator operand} {found : source.lookupExpression? operand = some childNode}
      {inputType : childNode.type = operandType} {outputType : node.type = resultType}
      {profile : CompatibleExpressionPrimitives.UnaryProfile operator operandType resultType core}
      {child : Certificate policy body compilation readFuel values source context reasonAt scope operand ⟨core.operandType, childCode⟩}
      (inside : Indexes (indexScope := indexScope) indexed indexKeyFound indexForm indexSourceType indexScalar child) :
      Indexes (indexScope := indexScope) indexed indexKeyFound indexForm indexSourceType indexScalar (.unary actual form found inputType outputType profile child)
  | binary_left {scope id node left right leftNode rightNode operator operandType resultType mode leftCode rightCode}
      {actual : CompatibleExpressionPrimitives.Metadata values.checked source id node (mode.resultType operator)}
      {form : node.form = .binary left operator right}
      {leftFound : source.lookupExpression? left = some leftNode} {rightFound : source.lookupExpression? right = some rightNode}
      {leftType : leftNode.type = operandType} {rightType : rightNode.type = operandType} {outputType : node.type = resultType}
      {profile : CompatibleExpressionPrimitives.BinaryProfile operator operandType resultType mode}
      {first : Certificate policy body compilation readFuel values source context reasonAt scope left ⟨mode.operandType operator, leftCode⟩}
      {second : Certificate policy body compilation readFuel values source context reasonAt scope right ⟨mode.operandType operator, rightCode⟩}
      (inside : Indexes (indexScope := indexScope) indexed indexKeyFound indexForm indexSourceType indexScalar first) :
      Indexes (indexScope := indexScope) indexed indexKeyFound indexForm indexSourceType indexScalar (.binary actual form leftFound rightFound leftType rightType outputType profile first second)
  | binary_right {scope id node left right leftNode rightNode operator operandType resultType mode leftCode rightCode}
      {actual : CompatibleExpressionPrimitives.Metadata values.checked source id node (mode.resultType operator)}
      {form : node.form = .binary left operator right}
      {leftFound : source.lookupExpression? left = some leftNode} {rightFound : source.lookupExpression? right = some rightNode}
      {leftType : leftNode.type = operandType} {rightType : rightNode.type = operandType} {outputType : node.type = resultType}
      {profile : CompatibleExpressionPrimitives.BinaryProfile operator operandType resultType mode}
      {first : Certificate policy body compilation readFuel values source context reasonAt scope left ⟨mode.operandType operator, leftCode⟩}
      {second : Certificate policy body compilation readFuel values source context reasonAt scope right ⟨mode.operandType operator, rightCode⟩}
      (inside : Indexes (indexScope := indexScope) indexed indexKeyFound indexForm indexSourceType indexScalar second) :
      Indexes (indexScope := indexScope) indexed indexKeyFound indexForm indexSourceType indexScalar (.binary actual form leftFound rightFound leftType rightType outputType profile first second)
  | conditional_condition {scope id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode}
      {actual : CompatibleExpressionPrimitives.Metadata values.checked source id node type}
      {form : node.form = .conditional condition thenId elseId}
      {conditionFound : source.lookupExpression? condition = some conditionNode}
      {thenFound : source.lookupExpression? thenId = some thenNode} {elseFound : source.lookupExpression? elseId = some elseNode}
      {conditionType : conditionNode.type = .bool} {thenType : thenNode.type = node.type} {elseType : elseNode.type = node.type}
      {conditionTree : Certificate policy body compilation readFuel values source context reasonAt scope condition ⟨.bool, conditionCode⟩}
      {thenTree : Certificate policy body compilation readFuel values source context reasonAt scope thenId ⟨type, thenCode⟩} {elseTree : Certificate policy body compilation readFuel values source context reasonAt scope elseId ⟨type, elseCode⟩}
      (inside : Indexes (indexScope := indexScope) indexed indexKeyFound indexForm indexSourceType indexScalar conditionTree) :
      Indexes (indexScope := indexScope) indexed indexKeyFound indexForm indexSourceType indexScalar (.conditional actual form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree)
  | conditional_then {scope id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode}
      {actual : CompatibleExpressionPrimitives.Metadata values.checked source id node type}
      {form : node.form = .conditional condition thenId elseId}
      {conditionFound : source.lookupExpression? condition = some conditionNode}
      {thenFound : source.lookupExpression? thenId = some thenNode} {elseFound : source.lookupExpression? elseId = some elseNode}
      {conditionType : conditionNode.type = .bool} {thenType : thenNode.type = node.type} {elseType : elseNode.type = node.type}
      {conditionTree : Certificate policy body compilation readFuel values source context reasonAt scope condition ⟨.bool, conditionCode⟩}
      {thenTree : Certificate policy body compilation readFuel values source context reasonAt scope thenId ⟨type, thenCode⟩} {elseTree : Certificate policy body compilation readFuel values source context reasonAt scope elseId ⟨type, elseCode⟩}
      (inside : Indexes (indexScope := indexScope) indexed indexKeyFound indexForm indexSourceType indexScalar thenTree) :
      Indexes (indexScope := indexScope) indexed indexKeyFound indexForm indexSourceType indexScalar (.conditional actual form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree)
  | conditional_else {scope id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode}
      {actual : CompatibleExpressionPrimitives.Metadata values.checked source id node type}
      {form : node.form = .conditional condition thenId elseId}
      {conditionFound : source.lookupExpression? condition = some conditionNode}
      {thenFound : source.lookupExpression? thenId = some thenNode} {elseFound : source.lookupExpression? elseId = some elseNode}
      {conditionType : conditionNode.type = .bool} {thenType : thenNode.type = node.type} {elseType : elseNode.type = node.type}
      {conditionTree : Certificate policy body compilation readFuel values source context reasonAt scope condition ⟨.bool, conditionCode⟩}
      {thenTree : Certificate policy body compilation readFuel values source context reasonAt scope thenId ⟨type, thenCode⟩} {elseTree : Certificate policy body compilation readFuel values source context reasonAt scope elseId ⟨type, elseCode⟩}
      (inside : Indexes (indexScope := indexScope) indexed indexKeyFound indexForm indexSourceType indexScalar elseTree) :
      Indexes (indexScope := indexScope) indexed indexKeyFound indexForm indexSourceType indexScalar (.conditional actual form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree)


  | index_base {scope id node base key baseNode keyNode layout comparison first second}
      {header : CompatibleExpressionIndices.Header values source id base node baseNode layout comparison first second}
      {keyFound : source.lookupExpression? key = some keyNode}
      {form : node.form = .index base key}
      {sourceType : baseNode.type = .mapping keyNode.type node.type}
      {scalar : CompatibleExpressionIndices.SourceScalar keyNode.type}
      {firstTree : Certificate policy body compilation readFuel values source context reasonAt scope base first}
      {secondTree : Certificate policy body compilation readFuel values source context reasonAt scope key second}
      (inside : Indexes (indexScope := indexScope) indexed indexKeyFound indexForm indexSourceType indexScalar firstTree) :
      Indexes (indexScope := indexScope) indexed indexKeyFound indexForm indexSourceType indexScalar (.index header keyFound form sourceType scalar firstTree secondTree)
  | index_key {scope id node base key baseNode keyNode layout comparison first second}
      {header : CompatibleExpressionIndices.Header values source id base node baseNode layout comparison first second}
      {keyFound : source.lookupExpression? key = some keyNode}
      {form : node.form = .index base key}
      {sourceType : baseNode.type = .mapping keyNode.type node.type}
      {scalar : CompatibleExpressionIndices.SourceScalar keyNode.type}
      {firstTree : Certificate policy body compilation readFuel values source context reasonAt scope base first}
      {secondTree : Certificate policy body compilation readFuel values source context reasonAt scope key second}
      (inside : Indexes (indexScope := indexScope) indexed indexKeyFound indexForm indexSourceType indexScalar secondTree) :
      Indexes (indexScope := indexScope) indexed indexKeyFound indexForm indexSourceType indexScalar (.index header keyFound form sourceType scalar firstTree secondTree)

/-- The legacy grammar excludes mapping access without a runtime assumption. -/
def NoIndexes {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {lowered : SourceCoreBasic.LoweredExpr}
    (root : Certificate policy body compilation readFuel values source context reasonAt scope id lowered) : Prop :=
  ∀ {indexScope indexId base key node baseNode keyNode layout comparison first second}
    (indexed : CompatibleExpressionIndices.Header values source indexId base node baseNode layout comparison first second)
    (keyFound : source.lookupExpression? key = some keyNode)
    (form : node.form = .index base key)
    (sourceType : baseNode.type = .mapping keyNode.type node.type)
    (scalar : CompatibleExpressionIndices.SourceScalar keyNode.type),
    Indexes (indexScope := indexScope) indexed keyFound form sourceType scalar root → False

private theorem product_policy_on {scope : SourceCoreLocalCell.Scope} {allowed : ExpressionId → Prop}
    (policyFor : PolicyOn policy compilation readFuel values source scope reasonAt allowed) :
    CompatibleExpressionProducts.PolicyOn policy compilation readFuel values source scope reasonAt allowed :=
  ⟨fun id admitted tree => policyFor.special id admitted (.leaf tree),
   fun id admitted tree => policyFor.read id admitted (.leaf tree), policyFor.lower, policyFor.leaf⟩

private theorem general_product_policy_on {scope : SourceCoreLocalCell.Scope} {allowed : ExpressionId → Prop}
    (policyFor : GeneralPolicyOn policy compilation readFuel values source scope reasonAt allowed) :
    CompatibleExpressionProducts.PolicyOn policy compilation readFuel values source scope reasonAt allowed :=
  ⟨fun id admitted tree => policyFor.special id admitted (.leaf tree),
   fun id admitted tree => policyFor.read id admitted (.leaf tree), policyFor.lower, policyFor.leaf⟩

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) : ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem ensure_type {site : SourceCoreElaboration.ErrorSite} {expected actual : Ty}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  by_cases same : expected = actual
  · exact same
  · simp [SourceCoreBasic.ensureType, same] at accepted

private theorem group_step {fuel : Nat} {scope : SourceCoreLocalCell.Scope} {id inner : ExpressionId}
    {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (found : source.lookupExpression? id = some node) (form : node.form = .group inner)
    (special : ∀ child budget, (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower compilation child budget source scope id reasonAt) = .ok none)
    (readPolicy : policy.readExpression source id =
      SourceCoreCompatibleDataExpressions.readExpression values.checked source id)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body (fuel + 1) compilation
      source scope id reasonAt = .ok lowered) :
    CompatibleExpressionPrimitives.Metadata values.checked source id node lowered.type ∧
      SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation
        source scope inner reasonAt = .ok lowered := by
  rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  by_cases owner : id.occurrence.owner = source.owner
  · simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte, found,
      bind, Except.bind, pure, Except.pure] at accepted
    have bypass := special (fun budget childSource childScope childId childReasonAt =>
      SourceCoreFunctions.lowerExpressionWithPolicy policy body (min budget fuel) compilation
        childSource childScope childId childReasonAt) (fuel + 1)
    cases hook : policy.lowerSpecial? <;> simp only [hook] at accepted bypass
    all_goals try rw [bypass] at accepted
    all_goals
      simp only [form, readPolicy] at accepted
      cases read : SourceCoreCompatibleDataExpressions.readExpression values.checked source id with
      | error => simp [read] at accepted
      | ok pair =>
        obtain ⟨other, type⟩ := pair
        have metadata := CompatibleExpressionReads.metadata_of_read read
        have same := Option.some.inj (metadata.found.symm.trans found)
        subst other
        simp only [read, form] at accepted
        obtain ⟨child, generated, rest⟩ := bind_ok accepted
        obtain ⟨checked, checkedType, output⟩ := bind_ok rest
        cases checked
        have same := ensure_type checkedType
        subst type
        simp only [Except.ok.injEq] at output
        subst lowered
        exact ⟨metadata, generated⟩
  · simp [owner, bind, Except.bind] at accepted

private theorem call_read {fuel : Nat} {scope : SourceCoreLocalCell.Scope}
    {id callee : ExpressionId} {ids : List ExpressionId} {resolution : IndirectCallResolution}
    {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee ids (.indirect resolution))
    (special : ∀ child budget, (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower compilation child budget source scope id reasonAt) = .ok none)
    (readPolicy : policy.readExpression source id =
      SourceCoreCompatibleDataExpressions.readExpression values.checked source id)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body (fuel + 1) compilation
      source scope id reasonAt = .ok lowered) :
    ∃ type, policy.readExpression source id = .ok (node, type) := by
  rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  by_cases owner : id.occurrence.owner = source.owner
  · simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte, found,
      bind, Except.bind, pure, Except.pure] at accepted
    have bypass := special (fun budget childSource childScope childId childReasonAt =>
      SourceCoreFunctions.lowerExpressionWithPolicy policy body (min budget fuel) compilation
        childSource childScope childId childReasonAt) (fuel + 1)
    cases hook : policy.lowerSpecial? <;> simp only [hook] at accepted bypass
    all_goals try rw [bypass] at accepted
    all_goals
      simp only [form, readPolicy] at accepted
      cases read : SourceCoreCompatibleDataExpressions.readExpression values.checked source id with
      | error => simp [read] at accepted
      | ok pair =>
        obtain ⟨other, type⟩ := pair
        have metadata := CompatibleExpressionReads.metadata_of_read read
        have same := Option.some.inj (metadata.found.symm.trans found)
        subst other
        exact ⟨type, readPolicy.trans read⟩
  · simp [owner, bind, Except.bind] at accepted

private theorem child_certificates {scope : SourceCoreLocalCell.Scope} {budget : Nat}
    {ids : List ExpressionId} {types : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    {certificate : ExpressionId → SourceCoreBasic.LoweredExpr → Prop}
    (unique : NodeOccurrencesUnique source) (typed : ExpressionsHaveTypes source context ids types)
    (generated : ids.mapM (fun id => SourceCoreFunctions.lowerExpressionWithPolicy policy body budget
      compilation source scope id reasonAt) = .ok codes)
    (extract : ∀ id, id ∈ ids → ∀ node code, source.lookupExpression? id = some node →
      ExpressionHasType source context id node.type →
      SourceCoreFunctions.lowerExpressionWithPolicy policy body budget compilation source scope id reasonAt = .ok code →
      certificate id code) :
    ids.length = types.length ∧ CompatibleExpressionConstructors.Nodes source ids types codes ∧
      ∀ id code, (id, code) ∈ ids.zip codes → certificate id code := by
  induction ids generalizing types codes with
  | nil =>
    cases typed
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at generated
    subst codes
    exact ⟨rfl, .nil, by simp⟩
  | cons id ids ih =>
    cases typed with
    | @cons _ _ _ type types head tail =>
      rw [List.mapM_cons] at generated
      obtain ⟨code, first, generated⟩ := bind_ok generated
      obtain ⟨restCodes, rest, generated⟩ := bind_ok generated
      cases generated
      obtain ⟨node, contains, sourceType⟩ := head.stored_type
      have found := lookupExpression?_complete unique contains
      have child := extract id (by simp) node code found (sourceType ▸ head) first
      obtain ⟨count, nodes, children⟩ := ih tail rest (fun id member => extract id (by simp [member]))
      refine ⟨congrArg Nat.succ count, .cons ⟨node, found, sourceType⟩ nodes, ?_⟩
      intro other otherCode member
      rcases List.mem_cons.mp member with same | remaining
      · cases same; exact child
      · exact children other otherCode remaining

/-- The actual successful action supplies every recursive compiler child.
Independent raw Source typing supplies child types before their extraction. -/
theorem of_functions_on_projected {scope : SourceCoreLocalCell.Scope}
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {allowed : ExpressionId → Prop}
    (policyFor : PolicyOn policy compilation readFuel values source scope reasonAt allowed)
    (closed : ∀ {parent node child}, allowed parent → source.lookupExpression? parent = some node →
      (.expression child : NodeId) ∈ node.form.references → allowed child)
    (coercions : ∀ id node, allowed id → Syntax source id → source.lookupExpression? id = some node → node.coercions = [])
    {id : ExpressionId} (syntaxTree : Syntax source id) (admitted : allowed id)
    {node : ExpressionNode} (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source context id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation
      source scope id reasonAt = .ok lowered) :
    Certificate policy body compilation readFuel values source context reasonAt scope id lowered ∧
      values.checked.catalog.project node.type = .ok lowered.type := by
  revert admitted
  induction syntaxTree generalizing node fuel lowered with
  | leaf tree =>
    intro admitted
    obtain ⟨tree, sites⟩ := CallableIndexedOwnedPreparedStagedReadProductTreeBounds.of_functions_on
      unique declarations (product_policy_on policyFor) closed
      (fun id node allowed tree found => coercions id node allowed (.leaf tree) found) tree admitted found typed accepted
    exact ⟨.leaf ⟨tree, sites⟩, (CompatibleExpressionPrimitives.Tree.product tree).projected found⟩
  | group originalFound form child ih =>
    intro admitted
    have same := Option.some.inj (originalFound.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      obtain ⟨metadata, generated⟩ := group_step originalFound form
        (policyFor.special _ admitted (.group originalFound form child))
        (policyFor.read _ admitted (.group originalFound form child)) accepted
      obtain ⟨innerNode, innerFound, sourceType, childTyped⟩ :=
        CompatibleExpressionProducts.group_source_types unique originalFound form metadata.coercions typed
      exact ⟨.group metadata form innerFound sourceType (ih innerFound childTyped generated
        (closed admitted originalFound (by simp [form, ExpressionForm.references]))).1, metadata.projected⟩
  | tuple originalFound form children ih =>
    intro admitted
    have same := Option.some.inj (originalFound.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      obtain ⟨codes, generated, rfl, metadata⟩ := CompatibleExpressionTuples.of_functions
        originalFound form (policyFor.special _ admitted (.tuple originalFound form children))
        (policyFor.read _ admitted (.tuple originalFound form children)) policyFor.leaf accepted
      obtain ⟨types, childTyped, sourceType⟩ := CompatibleExpressionTuples.source_types
        unique originalFound form metadata.coercions typed
      obtain ⟨count, nodes, certified⟩ := child_certificates unique childTyped generated
        (fun child member childNode code childFound childTyped childAccepted =>
          (ih child member childFound childTyped childAccepted
            (closed admitted originalFound (by simp [form, ExpressionForm.references, member]))).1)
      refine ⟨.tuple ⟨metadata, form, sourceType⟩
        (CompatibleExpressionConstructors.sequence_of_nodes count nodes
          (fun child code member => (⟨rfl, member⟩ : RecursiveStageTupleMeaning.Entries scope
            (_root_.List.zip _ _) scope child code))) certified, metadata.projected⟩
  | constructor originalFound form ranges children ih =>
    intro admitted
    have same := Option.some.inj (originalFound.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      obtain ⟨tag, headerWord, codes, rfl, receipt, count, arguments⟩ :=
        CompatibleExpressionConstructors.constructor_of_functions originalFound form
          (policyFor.special _ admitted (.constructor originalFound form ranges children))
          (policyFor.read _ admitted (.constructor originalFound form ranges children)) policyFor.leaf accepted
      obtain ⟨admissible, argumentsTyped, _sourceType⟩ :=
        CompatibleExpressionConstructors.constructor_source_types unique originalFound form receipt.metadata.coercions typed
      obtain ⟨nodes, certified⟩ := CompatibleExpressionConstructors.child_certificates unique argumentsTyped arguments
        (fun child member childNode code childFound childTyped childAccepted =>
          (ih child member childFound childTyped childAccepted
            (closed admitted originalFound (by simp [form, ExpressionForm.references, member]))).1)
      exact ⟨.constructor receipt form admissible ranges count nodes
        (CompatibleExpressionConstructors.sequence_of_nodes count nodes
          (fun child code member => (⟨rfl, member⟩ : RecursiveStageTupleMeaning.Entries scope
            (_root_.List.zip _ _) scope child code))) certified, receipt.metadata.projected⟩
  | @call callId _original _callee _ids _metadata originalFound form calleeSyntax children calleeIH ih =>
    intro admitted
    have same := Option.some.inj (originalFound.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      have special := policyFor.special _ admitted (.call originalFound form calleeSyntax children)
      have readPolicy := policyFor.read _ admitted (.call originalFound form calleeSyntax children)
      obtain ⟨type, read⟩ := call_read originalFound form special readPolicy accepted
      obtain ⟨compiler⟩ := CallableIndirectCallCertificates.of_functions originalFound form special read form accepted
      have parent := CallableIndexedOwnedPreparedStagedRecursiveCallerSourceReceipts.source_parent compiler readPolicy
      have originalSame := Option.some.inj (compiler.found.symm.trans originalFound)
      have parentTyped : ExpressionHasType source context callId compiler.original.type := by
        simpa [originalSame] using typed
      obtain ⟨parameter, result, types, calleeTyped, argumentsTyped, _bundle, _result⟩ :=
        CallableIndexedOwnedPreparedStagedRecursiveCallerSourceReceipts.original_child_types
          compiler parent unique parentTyped
      obtain ⟨calleeNode, contains, sourceType⟩ := calleeTyped.stored_type
      have calleeFound := lookupExpression?_complete unique contains
      have calleeCertified := (calleeIH calleeFound (sourceType ▸ calleeTyped) compiler.calleeAccepted
        (closed admitted originalFound (by simp [form, ExpressionForm.references]))).1
      obtain ⟨count, nodes, certified⟩ := child_certificates unique argumentsTyped compiler.argumentsAccepted
        (fun child member childNode code childFound childTyped childAccepted =>
          (ih child member childFound childTyped childAccepted
            (closed admitted originalFound (by simp [form, ExpressionForm.references, member]))).1)
      constructor
      · refine .call compiler (CompatibleExpressionConstructors.sequence_of_nodes count nodes ?_) ?_
        · intro child code member
          exact ⟨rfl, List.mem_cons_of_mem _ member⟩
        · intro child code member
          rcases List.mem_cons.mp member with head | remaining
          · cases head; exact calleeCertified
          · exact certified child code remaining
      · obtain ⟨_same, metadata⟩ := CallableIndexedOwnedPreparedStagedRecursiveCallerSourceReceipts.original_read_metadata compiler readPolicy
        rw [compiler.output]
        simpa only [originalSame] using metadata.projected

  | unary originalFound form child ih =>
    intro admitted
    have same := Option.some.inj (originalFound.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      have step := CompatibleExpressionConditionals.step_of_functions originalFound (by rw [form]; constructor)
        (policyFor.special _ admitted (.unary originalFound form child))
        (policyFor.read _ admitted (.unary originalFound form child)) accepted
      cases step with
      | @unary operator operand compiled otherForm metadata generated inputChecked =>
        obtain ⟨rfl, rfl⟩ := ExpressionForm.unary.inj (form.symm.trans otherForm)
        obtain ⟨childNode, core, childFound, childTyped, profile⟩ :=
          CompatibleExpressionPrimitives.unary_source_types unique originalFound form metadata.coercions metadata.requirements typed
        obtain ⟨childTree, projected⟩ := ih childFound childTyped generated
          (closed admitted originalFound (by simp [form, ExpressionForm.references]))
        have chosen := CompatibleExpressionConditionals.unary_selected profile projected
        rw [chosen] at metadata inputChecked ⊢
        obtain ⟨childType, childCode⟩ := compiled
        dsimp only at inputChecked childTree ⊢
        subst childType
        exact ⟨.unary metadata form childFound rfl rfl profile childTree, metadata.projected⟩
      | binary otherForm _ _ _ _ _ | group otherForm _ _ | pair otherForm _ _ _ | conditional otherForm _ _ _ _ => simp [form] at otherForm
  | binary originalFound form leftSyntax rightSyntax leftIH rightIH =>
    intro admitted
    have same := Option.some.inj (originalFound.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      have step := CompatibleExpressionConditionals.step_of_functions originalFound (by rw [form]; constructor)
        (policyFor.special _ admitted (.binary originalFound form leftSyntax rightSyntax))
        (policyFor.read _ admitted (.binary originalFound form leftSyntax rightSyntax)) accepted
      cases step with
      | @binary operator left right first second otherForm metadata firstGenerated secondGenerated leftChecked rightChecked =>
        obtain ⟨rfl, rfl, rfl⟩ := ExpressionForm.binary.inj (form.symm.trans otherForm)
        obtain ⟨leftNode, rightNode, mode, leftFound, rightFound, sameType, leftTyped, rightTyped, profile⟩ :=
          CompatibleExpressionPrimitives.binary_source_types unique originalFound form metadata.coercions metadata.requirements typed
        obtain ⟨firstTree, projected⟩ := leftIH leftFound leftTyped firstGenerated
          (closed admitted originalFound (by simp [form, ExpressionForm.references]))
        obtain ⟨secondTree, _projected⟩ := rightIH rightFound rightTyped secondGenerated
          (closed admitted originalFound (by simp [form, ExpressionForm.references]))
        have chosen := CompatibleExpressionConditionals.binary_selected profile projected
        rw [chosen] at metadata leftChecked rightChecked ⊢
        obtain ⟨firstType, leftCode⟩ := first
        obtain ⟨secondType, rightCode⟩ := second
        dsimp only at leftChecked rightChecked firstTree secondTree ⊢
        subst firstType secondType
        exact ⟨.binary metadata form leftFound rightFound rfl sameType.symm rfl profile firstTree secondTree, metadata.projected⟩
      | unary otherForm _ _ _ | group otherForm _ _ | pair otherForm _ _ _ | conditional otherForm _ _ _ _ => simp [form] at otherForm
  | conditional originalFound form conditionSyntax thenSyntax elseSyntax conditionIH thenIH elseIH =>
    intro admitted
    have same := Option.some.inj (originalFound.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      have step := CompatibleExpressionConditionals.step_of_functions originalFound (by rw [form]; constructor)
        (policyFor.special _ admitted (.conditional originalFound form conditionSyntax thenSyntax elseSyntax))
        (policyFor.read _ admitted (.conditional originalFound form conditionSyntax thenSyntax elseSyntax)) accepted
      cases step with
      | @conditional condition thenId elseId conditionCode thenCode elseCode type otherForm metadata conditionGenerated thenGenerated elseGenerated =>
        obtain ⟨rfl, rfl, rfl⟩ := ExpressionForm.conditional.inj (form.symm.trans otherForm)
        obtain ⟨conditionNode, thenNode, elseNode, conditionFound, thenFound, elseFound, conditionType, thenType, elseType,
          conditionTyped, thenTyped, elseTyped⟩ := CompatibleExpressionConditionals.conditional_source_types unique originalFound form metadata.coercions typed
        obtain ⟨conditionTree, _⟩ := conditionIH conditionFound conditionTyped conditionGenerated
          (closed admitted originalFound (by simp [form, ExpressionForm.references]))
        obtain ⟨thenTree, _⟩ := thenIH thenFound thenTyped thenGenerated
          (closed admitted originalFound (by simp [form, ExpressionForm.references]))
        obtain ⟨elseTree, _⟩ := elseIH elseFound elseTyped elseGenerated
          (closed admitted originalFound (by simp [form, ExpressionForm.references]))
        exact ⟨.conditional metadata form conditionFound thenFound elseFound conditionType thenType elseType
          conditionTree thenTree elseTree, metadata.projected⟩
      | unary otherForm _ _ _ | binary otherForm _ _ _ _ _ | group otherForm _ _ | pair otherForm _ _ _ => simp [form] at otherForm


theorem of_functions_on {scope : SourceCoreLocalCell.Scope}
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {allowed : ExpressionId → Prop}
    (policyFor : PolicyOn policy compilation readFuel values source scope reasonAt allowed)
    (closed : ∀ {parent node child}, allowed parent → source.lookupExpression? parent = some node →
      (.expression child : NodeId) ∈ node.form.references → allowed child)
    (coercions : ∀ id node, allowed id → Syntax source id → source.lookupExpression? id = some node → node.coercions = [])
    {id : ExpressionId} (syntaxTree : Syntax source id) (admitted : allowed id)
    {node : ExpressionNode} (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source context id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation
      source scope id reasonAt = .ok lowered) :
    Certificate policy body compilation readFuel values source context reasonAt scope id lowered := by
  exact (of_functions_on_projected unique declarations policyFor closed coercions
    syntaxTree admitted found typed accepted).1

theorem of_functions {scope : SourceCoreLocalCell.Scope}
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (policyFor : PolicyFor policy compilation readFuel values source scope reasonAt)
    (coercions : ∀ id node, Syntax source id → source.lookupExpression? id = some node → node.coercions = [])
    {id : ExpressionId} (syntaxTree : Syntax source id)
    {node : ExpressionNode} (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source context id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation
      source scope id reasonAt = .ok lowered) :
    Certificate policy body compilation readFuel values source context reasonAt scope id lowered := by
  exact of_functions_on unique declarations (policyFor.on (fun _ => True))
    (fun _ _ _ => trivial) (fun id node _ tree found => coercions id node tree found)
    syntaxTree trivial found typed accepted

/-- The actual successful action supplies every recursive compiler child.
Independent raw Source typing supplies child types before their extraction. -/
private theorem projected_children
    {fuel : Nat} {scope : SourceCoreLocalCell.Scope}
    {ids : List ExpressionId} {types : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    (unique : NodeOccurrencesUnique source) (typed : ExpressionsHaveTypes source context ids types)
    (generated : ids.mapM (fun id => SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope id reasonAt) = .ok codes)
    (extract : ∀ id, id ∈ ids → ∀ node code, source.lookupExpression? id = some node →
      ExpressionHasType source context id node.type →
      SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope id reasonAt = .ok code →
      Certificate policy body compilation readFuel values source context reasonAt scope id code ∧
        values.checked.catalog.project node.type = .ok code.type) :
    ids.length = types.length ∧ CompatibleExpressionConstructors.Nodes source ids types codes ∧
      types.mapM values.checked.catalog.project = .ok (codes.map (·.type)) ∧
      ∀ id code, (id, code) ∈ ids.zip codes →
        Certificate policy body compilation readFuel values source context reasonAt scope id code := by
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
      obtain ⟨code, first, generated⟩ := bind_ok generated
      obtain ⟨restCodes, rest, generated⟩ := bind_ok generated
      cases generated
      obtain ⟨node, contains, sourceType⟩ := head.stored_type
      have found := lookupExpression?_complete unique contains
      have child := extract id (by simp) node code found (sourceType ▸ head) first
      obtain ⟨count, nodes, projected, children⟩ := ih tail rest (fun id member => extract id (by simp [member]))
      refine ⟨congrArg Nat.succ count, .cons ⟨node, found, sourceType⟩ nodes, ?_, ?_⟩
      · simp [List.mapM_cons, ← sourceType, child.2, projected, bind, Except.bind]
      · intro other otherCode member
        rcases List.mem_cons.mp member with same | remaining
        · cases same; exact child.1
        · exact children other otherCode remaining

theorem of_general_functions_on_projected {scope : SourceCoreLocalCell.Scope}
    (native : SourceCoreGeneralFunctions.CallableContext) (active : TypeSystem.Substitution)
    (callables : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some native) active)
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {allowed : ExpressionId → Prop}
    (policyFor : GeneralPolicyOn policy compilation readFuel values source scope reasonAt allowed)
    (closed : ∀ {parent node child}, allowed parent → source.lookupExpression? parent = some node →
      (.expression child : NodeId) ∈ node.form.references → allowed child)
    (coercions : ∀ id node, allowed id → GeneralSyntax source id → source.lookupExpression? id = some node → node.coercions = [])
    {id : ExpressionId} (syntaxTree : GeneralSyntax source id) (admitted : allowed id)
    {node : ExpressionNode} (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source context id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation
      source scope id reasonAt = .ok lowered) :
    Certificate policy body compilation readFuel values source context reasonAt scope id lowered ∧
      values.checked.catalog.project node.type = .ok lowered.type := by
  revert admitted
  induction syntaxTree generalizing node fuel lowered with
  | leaf tree =>
    intro admitted
    obtain ⟨tree, sites⟩ := CallableIndexedOwnedPreparedStagedReadProductTreeBounds.of_functions_on
      unique declarations (general_product_policy_on policyFor) closed
      (fun id node allowed tree found => coercions id node allowed (.leaf tree) found) tree admitted found typed accepted
    exact ⟨.leaf ⟨tree, sites⟩, (CompatibleExpressionPrimitives.Tree.product tree).projected found⟩
  | group originalFound form child ih =>
    intro admitted
    have same := Option.some.inj (originalFound.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      obtain ⟨metadata, generated⟩ := group_step originalFound form
        (policyFor.special _ admitted (.group originalFound form child))
        (policyFor.read _ admitted (.group originalFound form child)) accepted
      obtain ⟨innerNode, innerFound, sourceType, childTyped⟩ :=
        CompatibleExpressionProducts.group_source_types unique originalFound form metadata.coercions typed
      exact ⟨.group metadata form innerFound sourceType (ih innerFound childTyped generated
        (closed admitted originalFound (by simp [form, ExpressionForm.references]))).1, metadata.projected⟩
  | tuple originalFound form children ih =>
    intro admitted
    have same := Option.some.inj (originalFound.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      obtain ⟨codes, generated, rfl, metadata⟩ := CompatibleExpressionTuples.of_functions
        originalFound form (policyFor.special _ admitted (.tuple originalFound form children))
        (policyFor.read _ admitted (.tuple originalFound form children)) policyFor.leaf accepted
      obtain ⟨types, childTyped, sourceType⟩ := CompatibleExpressionTuples.source_types
        unique originalFound form metadata.coercions typed
      obtain ⟨count, nodes, certified⟩ := child_certificates unique childTyped generated
        (fun child member childNode code childFound childTyped childAccepted =>
          (ih child member childFound childTyped childAccepted
            (closed admitted originalFound (by simp [form, ExpressionForm.references, member]))).1)
      refine ⟨.tuple ⟨metadata, form, sourceType⟩
        (CompatibleExpressionConstructors.sequence_of_nodes count nodes
          (fun child code member => (⟨rfl, member⟩ : RecursiveStageTupleMeaning.Entries scope
            (_root_.List.zip _ _) scope child code))) certified, metadata.projected⟩
  | constructor originalFound form ranges children ih =>
    intro admitted
    have same := Option.some.inj (originalFound.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      obtain ⟨tag, headerWord, codes, rfl, receipt, count, arguments⟩ :=
        CompatibleExpressionConstructors.constructor_of_functions originalFound form
          (policyFor.special _ admitted (.constructor originalFound form ranges children))
          (policyFor.read _ admitted (.constructor originalFound form ranges children)) policyFor.leaf accepted
      obtain ⟨admissible, argumentsTyped, _sourceType⟩ :=
        CompatibleExpressionConstructors.constructor_source_types unique originalFound form receipt.metadata.coercions typed
      obtain ⟨nodes, certified⟩ := CompatibleExpressionConstructors.child_certificates unique argumentsTyped arguments
        (fun child member childNode code childFound childTyped childAccepted =>
          (ih child member childFound childTyped childAccepted
            (closed admitted originalFound (by simp [form, ExpressionForm.references, member]))).1)
      exact ⟨.constructor receipt form admissible ranges count nodes
        (CompatibleExpressionConstructors.sequence_of_nodes count nodes
          (fun child code member => (⟨rfl, member⟩ : RecursiveStageTupleMeaning.Entries scope
            (_root_.List.zip _ _) scope child code))) certified, receipt.metadata.projected⟩
  | @builtin callId _original _callee _ids function originalFound form children ih =>
    intro admitted
    have same := Option.some.inj (originalFound.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      obtain ⟨compiler⟩ := CallableIndexedOwnedPreparedStagedBuiltinCallCertificates.of_functions
        native active callables originalFound form
        (policyFor.special _ admitted (.builtin originalFound form children))
        (policyFor.read _ admitted (.builtin originalFound form children)) accepted
      have originalSame := Option.some.inj (compiler.metadata.found.symm.trans originalFound)
      have parentTyped : ExpressionHasType source context callId compiler.node.type := by
        simpa only [originalSame] using typed
      obtain ⟨calleeTyped, argumentsTyped, sourceType⟩ :=
        CallableIndexedOwnedPreparedStagedBuiltinCallCertificates.source_types unique
          compiler.metadata.found compiler.form compiler.metadata.coercions parentTyped
      obtain ⟨count, nodes, projected, certified⟩ := projected_children unique argumentsTyped compiler.generated
        (fun child member childNode code childFound childTyped childAccepted =>
          ih child member childFound childTyped childAccepted
            (closed admitted originalFound (by simp [form, ExpressionForm.references, member])))
      rw [CompatibleBuiltinMeaning.argumentTypes_project function] at projected
      exact ⟨.builtin compiler calleeTyped sourceType (Except.ok.inj projected).symm
        (CompatibleExpressionConstructors.sequence_of_nodes count nodes
          (fun child code member => (⟨rfl, member⟩ : RecursiveStageTupleMeaning.Entries scope
            (_root_.List.zip _ _) scope child code))) certified,
        by simpa only [originalSame] using compiler.metadata.projected⟩
  | @direct callId _original _callee _ids _instantiation originalFound form monomorphic children ih =>
    intro admitted
    have same := Option.some.inj (originalFound.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      obtain ⟨compiler⟩ := CallableIndexedOwnedPreparedStagedDirectCallCertificates.of_functions
        originalFound form monomorphic
        (policyFor.special _ admitted (.direct originalFound form monomorphic children))
        (policyFor.read _ admitted (.direct originalFound form monomorphic children)) accepted
      have originalSame := Option.some.inj (compiler.metadata.found.symm.trans originalFound)
      have parentTyped : ExpressionHasType source context callId compiler.node.type := by
        simpa only [originalSame] using typed
      obtain ⟨types, calleeTyped, application, argumentsTyped⟩ :=
        CallableIndexedOwnedPreparedStagedDirectCallCertificates.source_types unique
          compiler.metadata.found compiler.form compiler.metadata.coercions parentTyped
      obtain ⟨count, nodes, certified⟩ := child_certificates unique argumentsTyped compiler.generated
        (fun child member childNode code childFound childTyped childAccepted =>
          (ih child member childFound childTyped childAccepted
            (closed admitted originalFound (by simp [form, ExpressionForm.references, member]))).1)
      exact ⟨.direct compiler calleeTyped application
        (CompatibleExpressionConstructors.sequence_of_nodes count nodes
          (fun child code member => (⟨rfl, member⟩ : RecursiveStageTupleMeaning.Entries scope
            (_root_.List.zip _ _) scope child code))) certified,
        by simpa only [originalSame] using compiler.metadata.projected⟩
  | @call callId _original _callee _ids _metadata originalFound form calleeSyntax children calleeIH ih =>
    intro admitted
    have same := Option.some.inj (originalFound.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      have special := policyFor.special _ admitted (.call originalFound form calleeSyntax children)
      have readPolicy := policyFor.read _ admitted (.call originalFound form calleeSyntax children)
      obtain ⟨type, read⟩ := call_read originalFound form special readPolicy accepted
      obtain ⟨compiler⟩ := CallableIndirectCallCertificates.of_functions originalFound form special read form accepted
      have parent := CallableIndexedOwnedPreparedStagedRecursiveCallerSourceReceipts.source_parent compiler readPolicy
      have originalSame := Option.some.inj (compiler.found.symm.trans originalFound)
      have parentTyped : ExpressionHasType source context callId compiler.original.type := by
        simpa [originalSame] using typed
      obtain ⟨parameter, result, types, calleeTyped, argumentsTyped, _bundle, _result⟩ :=
        CallableIndexedOwnedPreparedStagedRecursiveCallerSourceReceipts.original_child_types
          compiler parent unique parentTyped
      obtain ⟨calleeNode, contains, sourceType⟩ := calleeTyped.stored_type
      have calleeFound := lookupExpression?_complete unique contains
      have calleeCertified := (calleeIH calleeFound (sourceType ▸ calleeTyped) compiler.calleeAccepted
        (closed admitted originalFound (by simp [form, ExpressionForm.references]))).1
      obtain ⟨count, nodes, certified⟩ := child_certificates unique argumentsTyped compiler.argumentsAccepted
        (fun child member childNode code childFound childTyped childAccepted =>
          (ih child member childFound childTyped childAccepted
            (closed admitted originalFound (by simp [form, ExpressionForm.references, member]))).1)
      constructor
      · refine .call compiler (CompatibleExpressionConstructors.sequence_of_nodes count nodes ?_) ?_
        · intro child code member
          exact ⟨rfl, List.mem_cons_of_mem _ member⟩
        · intro child code member
          rcases List.mem_cons.mp member with head | remaining
          · cases head; exact calleeCertified
          · exact certified child code remaining
      · obtain ⟨_same, metadata⟩ := CallableIndexedOwnedPreparedStagedRecursiveCallerSourceReceipts.original_read_metadata compiler readPolicy
        rw [compiler.output]
        simpa only [originalSame] using metadata.projected

  | unary originalFound form child ih =>
    intro admitted
    have same := Option.some.inj (originalFound.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      have step := CompatibleExpressionConditionals.step_of_functions originalFound (by rw [form]; constructor)
        (policyFor.special _ admitted (.unary originalFound form child))
        (policyFor.read _ admitted (.unary originalFound form child)) accepted
      cases step with
      | @unary operator operand compiled otherForm metadata generated inputChecked =>
        obtain ⟨rfl, rfl⟩ := ExpressionForm.unary.inj (form.symm.trans otherForm)
        obtain ⟨childNode, core, childFound, childTyped, profile⟩ :=
          CompatibleExpressionPrimitives.unary_source_types unique originalFound form metadata.coercions metadata.requirements typed
        obtain ⟨childTree, projected⟩ := ih childFound childTyped generated
          (closed admitted originalFound (by simp [form, ExpressionForm.references]))
        have chosen := CompatibleExpressionConditionals.unary_selected profile projected
        rw [chosen] at metadata inputChecked ⊢
        obtain ⟨childType, childCode⟩ := compiled
        dsimp only at inputChecked childTree ⊢
        subst childType
        exact ⟨.unary metadata form childFound rfl rfl profile childTree, metadata.projected⟩
      | binary otherForm _ _ _ _ _ | group otherForm _ _ | pair otherForm _ _ _ | conditional otherForm _ _ _ _ => simp [form] at otherForm
  | binary originalFound form leftSyntax rightSyntax leftIH rightIH =>
    intro admitted
    have same := Option.some.inj (originalFound.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      have step := CompatibleExpressionConditionals.step_of_functions originalFound (by rw [form]; constructor)
        (policyFor.special _ admitted (.binary originalFound form leftSyntax rightSyntax))
        (policyFor.read _ admitted (.binary originalFound form leftSyntax rightSyntax)) accepted
      cases step with
      | @binary operator left right first second otherForm metadata firstGenerated secondGenerated leftChecked rightChecked =>
        obtain ⟨rfl, rfl, rfl⟩ := ExpressionForm.binary.inj (form.symm.trans otherForm)
        obtain ⟨leftNode, rightNode, mode, leftFound, rightFound, sameType, leftTyped, rightTyped, profile⟩ :=
          CompatibleExpressionPrimitives.binary_source_types unique originalFound form metadata.coercions metadata.requirements typed
        obtain ⟨firstTree, projected⟩ := leftIH leftFound leftTyped firstGenerated
          (closed admitted originalFound (by simp [form, ExpressionForm.references]))
        obtain ⟨secondTree, _projected⟩ := rightIH rightFound rightTyped secondGenerated
          (closed admitted originalFound (by simp [form, ExpressionForm.references]))
        have chosen := CompatibleExpressionConditionals.binary_selected profile projected
        rw [chosen] at metadata leftChecked rightChecked ⊢
        obtain ⟨firstType, leftCode⟩ := first
        obtain ⟨secondType, rightCode⟩ := second
        dsimp only at leftChecked rightChecked firstTree secondTree ⊢
        subst firstType secondType
        exact ⟨.binary metadata form leftFound rightFound rfl sameType.symm rfl profile firstTree secondTree, metadata.projected⟩
      | unary otherForm _ _ _ | group otherForm _ _ | pair otherForm _ _ _ | conditional otherForm _ _ _ _ => simp [form] at otherForm
  | conditional originalFound form conditionSyntax thenSyntax elseSyntax conditionIH thenIH elseIH =>
    intro admitted
    have same := Option.some.inj (originalFound.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      have step := CompatibleExpressionConditionals.step_of_functions originalFound (by rw [form]; constructor)
        (policyFor.special _ admitted (.conditional originalFound form conditionSyntax thenSyntax elseSyntax))
        (policyFor.read _ admitted (.conditional originalFound form conditionSyntax thenSyntax elseSyntax)) accepted
      cases step with
      | @conditional condition thenId elseId conditionCode thenCode elseCode type otherForm metadata conditionGenerated thenGenerated elseGenerated =>
        obtain ⟨rfl, rfl, rfl⟩ := ExpressionForm.conditional.inj (form.symm.trans otherForm)
        obtain ⟨conditionNode, thenNode, elseNode, conditionFound, thenFound, elseFound, conditionType, thenType, elseType,
          conditionTyped, thenTyped, elseTyped⟩ := CompatibleExpressionConditionals.conditional_source_types unique originalFound form metadata.coercions typed
        obtain ⟨conditionTree, _⟩ := conditionIH conditionFound conditionTyped conditionGenerated
          (closed admitted originalFound (by simp [form, ExpressionForm.references]))
        obtain ⟨thenTree, _⟩ := thenIH thenFound thenTyped thenGenerated
          (closed admitted originalFound (by simp [form, ExpressionForm.references]))
        obtain ⟨elseTree, _⟩ := elseIH elseFound elseTyped elseGenerated
          (closed admitted originalFound (by simp [form, ExpressionForm.references]))
        exact ⟨.conditional metadata form conditionFound thenFound elseFound conditionType thenType elseType
          conditionTree thenTree elseTree, metadata.projected⟩
      | unary otherForm _ _ _ | binary otherForm _ _ _ _ _ | group otherForm _ _ | pair otherForm _ _ _ => simp [form] at otherForm


  | @index id original base key keyNode originalFound form keyFound scalar firstSyntax secondSyntax firstIH secondIH =>
    intro admitted
    have same := Option.some.inj (originalFound.symm.trans found)
    subst node
    cases fuel with
    | zero => simp [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
    | succ fuel =>
      have syntaxTree : GeneralSyntax source id := .index originalFound form keyFound scalar firstSyntax secondSyntax
      obtain ⟨keyType, baseTyped, keyTyped⟩ := CompatibleExpressionIndices.index_source_types unique originalFound form
        (coercions _ _ admitted syntaxTree originalFound) typed
      obtain ⟨baseNode, baseContains, baseType⟩ := baseTyped.stored_type
      obtain ⟨actualKeyNode, keyContains, actualKeyType⟩ := keyTyped.stored_type
      have keySame := Option.some.inj ((lookupExpression?_complete unique keyContains).symm.trans keyFound)
      subst actualKeyNode
      have baseFound := lookupExpression?_complete unique baseContains
      rw [← actualKeyType] at keyTyped baseType baseTyped
      rw [← baseType] at baseTyped
      obtain ⟨layout, comparison, first, second, rfl, header, firstGenerated, secondGenerated⟩ :=
        CompatibleExpressionIndices.index_of_functions originalFound baseFound form
          (policyFor.special _ admitted syntaxTree) (policyFor.read _ admitted syntaxTree) policyFor.leaf accepted
      exact ⟨.index header keyFound form baseType scalar
        (firstIH baseFound baseTyped firstGenerated
          (closed admitted originalFound (by simp [form, ExpressionForm.references]))).1
        (secondIH keyFound keyTyped secondGenerated
          (closed admitted originalFound (by simp [form, ExpressionForm.references]))).1, header.metadata.projected⟩

theorem of_general_functions_on {scope : SourceCoreLocalCell.Scope}
    (native : SourceCoreGeneralFunctions.CallableContext) (active : TypeSystem.Substitution)
    (callables : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some native) active)
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {allowed : ExpressionId → Prop}
    (policyFor : GeneralPolicyOn policy compilation readFuel values source scope reasonAt allowed)
    (closed : ∀ {parent node child}, allowed parent → source.lookupExpression? parent = some node →
      (.expression child : NodeId) ∈ node.form.references → allowed child)
    (coercions : ∀ id node, allowed id → GeneralSyntax source id → source.lookupExpression? id = some node → node.coercions = [])
    {id : ExpressionId} (syntaxTree : GeneralSyntax source id) (admitted : allowed id)
    {node : ExpressionNode} (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source context id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation
      source scope id reasonAt = .ok lowered) :
    Certificate policy body compilation readFuel values source context reasonAt scope id lowered := by
  exact (of_general_functions_on_projected native active callables unique declarations policyFor closed coercions
    syntaxTree admitted found typed accepted).1

theorem of_general_functions {scope : SourceCoreLocalCell.Scope}
    (native : SourceCoreGeneralFunctions.CallableContext) (active : TypeSystem.Substitution)
    (callables : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some native) active)
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    (policyFor : GeneralPolicyFor policy compilation readFuel values source scope reasonAt)
    (coercions : ∀ id node, GeneralSyntax source id → source.lookupExpression? id = some node → node.coercions = [])
    {id : ExpressionId} (syntaxTree : GeneralSyntax source id)
    {node : ExpressionNode} (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source context id node.type)
    {fuel : Nat} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation
      source scope id reasonAt = .ok lowered) :
    Certificate policy body compilation readFuel values source context reasonAt scope id lowered := by
  exact of_general_functions_on native active callables unique declarations (policyFor.on (fun _ => True))
    (fun _ _ _ => trivial) (fun id node _ tree found => coercions id node tree found)
    syntaxTree trivial found typed accepted

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates
