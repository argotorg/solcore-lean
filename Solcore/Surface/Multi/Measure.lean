import Solcore.Surface.Multi.Syntax

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Solcore.Workspace

/-- The closed parser-side index of concrete AST carrier sorts. -/
inductive AstCarrierSort where
  | parsedModule
  | topItem
  | qualifiedName
  | identifier
  | pathComponent
  | externalLibraryName
  | syntaxMarker
  | unitMarker
  | moduleReference
  | importSelectorEntry
  | importSelection
  | hidingClause
  | importMode
  | importDecl
  | constructorSelection
  | exportItem
  | exportEntry
  | localExportList
  | remoteExportEntry
  | remoteExportSelection
  | exportMode
  | forallBinder
  | forallClause
  | predicate
  | genericPrefix
  | parameter
  | functionSignature
  | classMethodDecl
  | functionDecl
  | fallbackDecl
  | contractConstructorDecl
  | dataConstructor
  | dataDecl
  | typeAliasDecl
  | classDecl
  | instanceDecl
  | pragmaKind
  | pragmaDecl
  | fieldDecl
  | contractMember
  | contractDecl
  | literal
  | typeExpr
  | prefixOperator
  | infixOperator
  | assignmentOperator
  | expression
  | pattern
  | body
  | letBinding
  | forInitItem
  | forPostItem
  | matchArm
  | statement
  | assemblySlice
  deriving Repr, BEq, DecidableEq

/-- One located-wrapper or payload occurrence in the concrete AST carrier. -/
inductive AstCarrier where
  | located (sort : AstCarrierSort)
  | payload (sort : AstCarrierSort)
  deriving Repr, BEq, DecidableEq

private def measureList {α : Type} (measure : α → Nat)
    (values : List α) : Nat :=
  (values.map measure).sum

private def measureOption {α : Type} (measure : α → Nat) : Option α → Nat
  | none => 0
  | some value => measure value

private def measureNonemptyList {α : Type} (measure : α → Nat)
    (values : NonemptyList α) : Nat :=
  measure values.head + measureList measure values.tail

private def identifierMeasure (_ : IdentifierOccurrence) : Nat :=
  2

private def pathComponentMeasure (_ : PathComponent) : Nat :=
  2

private def externalLibraryNameMeasure
    (_ : Located ExternalLibraryName) : Nat :=
  2

private def markerMeasure (_ : Marker) : Nat :=
  2

private def unitMarkerMeasure (_ : Located Unit) : Nat :=
  2

private def pragmaKindMeasure (_ : Located PragmaKind) : Nat :=
  2

private def prefixOperatorMeasure (_ : Located PrefixOperator) : Nat :=
  2

private def infixOperatorMeasure (_ : Located InfixOperator) : Nat :=
  2

private def assignmentOperatorMeasure
    (_ : Located AssignmentOperator) : Nat :=
  2

private def assemblySliceMeasure (_ : AssemblySlice) : Nat :=
  2

private def qualifiedNameMeasure (name : QualifiedName) : Nat :=
  2 + measureNonemptyList identifierMeasure name.payload.components

private def moduleReferenceMeasure (reference : ModuleReference) : Nat :=
  2 +
    match reference.payload with
    | .relative components =>
        measureNonemptyList pathComponentMeasure components
    | .libraryRoot marker tail =>
        markerMeasure marker +
          measureNonemptyList pathComponentMeasure tail
    | .standard marker tail =>
        markerMeasure marker + measureList pathComponentMeasure tail
    | .external atMarker library tail =>
        markerMeasure atMarker +
          externalLibraryNameMeasure library +
          measureNonemptyList pathComponentMeasure tail

private def importSelectorEntryMeasure
    (entry : ImportSelectorEntry) : Nat :=
  2 +
    match entry.payload with
    | .wildcard marker => markerMeasure marker
    | .named source alias =>
        identifierMeasure source + measureOption identifierMeasure alias

private def importSelectionMeasure (selection : ImportSelection) : Nat :=
  2 + measureList importSelectorEntryMeasure selection.payload.entries

private def hidingClauseMeasure (clause : HidingClause) : Nat :=
  2 + measureList identifierMeasure clause.payload.names

private def importModeMeasure (mode : ImportMode) : Nat :=
  1 +
    match mode with
    | .module alias => measureOption identifierMeasure alias
    | .items selection hidingClause =>
        importSelectionMeasure selection +
          measureOption hidingClauseMeasure hidingClause

private def importDeclMeasure (declaration : ImportDecl) : Nat :=
  2 +
    moduleReferenceMeasure declaration.payload.moduleRef +
    importModeMeasure declaration.payload.mode

private def constructorSelectionMeasure
    (selection : ConstructorSelection) : Nat :=
  2 +
    match selection.payload with
    | .all marker => markerMeasure marker
    | .named constructors =>
        measureNonemptyList identifierMeasure constructors

private def exportItemMeasure (item : ExportItem) : Nat :=
  2 +
    identifierMeasure item.payload.name +
    measureOption constructorSelectionMeasure item.payload.constructors

private def exportEntryMeasure (entry : ExportEntry) : Nat :=
  2 +
    match entry.payload with
    | .wildcard marker => markerMeasure marker
    | .item item => exportItemMeasure item
    | .allFrom moduleRef marker =>
        moduleReferenceMeasure moduleRef + markerMeasure marker

private def localExportListMeasure (selection : LocalExportList) : Nat :=
  2 + measureList exportEntryMeasure selection.payload.entries

private def remoteExportEntryMeasure (entry : RemoteExportEntry) : Nat :=
  2 +
    match entry.payload with
    | .wildcard marker => markerMeasure marker
    | .item item => exportItemMeasure item

private def remoteExportSelectionMeasure
    (selection : RemoteExportSelection) : Nat :=
  2 +
    match selection.payload with
    | .dotWildcard marker => markerMeasure marker
    | .braced entries => measureList remoteExportEntryMeasure entries

private def exportModeMeasure (declaration : ExportDecl) : Nat :=
  2 +
    match declaration.payload with
    | .local selection => localExportListMeasure selection
    | .module moduleRef alias =>
        moduleReferenceMeasure moduleRef +
          measureOption identifierMeasure alias
    | .from moduleRef selection =>
        moduleReferenceMeasure moduleRef +
          remoteExportSelectionMeasure selection

private def literalMeasure (literal : Literal) : Nat :=
  1 +
    match literal.payload with
    | .decimal _ _ => 1
    | .hexadecimal _ _ => 1
    | .string _ _ => 1

mutual

private def typeExprPayloadMeasure : TypeExprPayload → Nat
  | .named name arguments =>
      1 + qualifiedNameMeasure name + typeExprArgumentsMeasure arguments
  | .proxy marker inner =>
      1 + unitMarkerMeasure marker + typeExprMeasure inner
  | .function domain codomain =>
      1 + typeExprMeasure domain + typeExprMeasure codomain
  | .tuple elements =>
      1 + typeExprListMeasure elements
  | .group inner =>
      1 + typeExprMeasure inner
  | .comptime marker inner =>
      1 + markerMeasure marker + typeExprMeasure inner

private def typeExprMeasure : TypeExpr → Nat
  | ⟨_, payload⟩ =>
      1 + typeExprPayloadMeasure payload

private def typeExprArgumentsMeasure :
    Option (NonemptyList TypeExpr) → Nat
  | none => 0
  | some arguments => typeExprNonemptyMeasure arguments

private def typeExprNonemptyMeasure : NonemptyList TypeExpr → Nat
  | ⟨head, tail⟩ =>
      typeExprMeasure head + typeExprListMeasure tail

private def typeExprListMeasure : List TypeExpr → Nat
  | [] => 0
  | head :: tail =>
      typeExprMeasure head + typeExprListMeasure tail

end

private def forallBinderMeasure (binder : ForallBinder) : Nat :=
  2 +
    match binder.payload with
    | .bare name => identifierMeasure name
    | .bounded name className arguments =>
        identifierMeasure name +
          qualifiedNameMeasure className +
          measureOption
            (measureNonemptyList typeExprMeasure)
            arguments

private def forallClauseMeasure (clause : ForallClause) : Nat :=
  2 + measureNonemptyList forallBinderMeasure clause.payload.binders

private def predicateMeasure (predicate : Predicate) : Nat :=
  2 +
    typeExprMeasure predicate.payload.main +
    qualifiedNameMeasure predicate.payload.className +
    measureOption
      (measureNonemptyList typeExprMeasure)
      predicate.payload.parameters

private def genericPrefixMeasure (genericPrefix : GenericPrefix) : Nat :=
  2 +
    forallClauseMeasure genericPrefix.payload.forallClause +
    measureOption
      (measureNonemptyList predicateMeasure)
      genericPrefix.payload.context

private def parameterMeasure (parameter : Parameter) : Nat :=
  2 +
    measureOption markerMeasure parameter.payload.comptime +
    identifierMeasure parameter.payload.name +
    measureOption typeExprMeasure parameter.payload.type

private def functionSignatureMeasure
    (signature : FunctionSignature) : Nat :=
  2 +
    measureOption genericPrefixMeasure signature.payload.genericPrefix +
    measureOption markerMeasure signature.payload.public +
    measureOption markerMeasure signature.payload.payable +
    identifierMeasure signature.payload.name +
    measureList parameterMeasure signature.payload.parameters +
    measureOption typeExprMeasure signature.payload.returnType

mutual

private def expressionPayloadMeasure : ExpressionPayload → Nat
  | .name name =>
      1 + identifierMeasure name
  | .call callee arguments =>
      1 + expressionMeasure callee + expressionListMeasure arguments
  | .select receiver field =>
      1 + expressionMeasure receiver + identifierMeasure field
  | .dotConstructor marker name arguments =>
      1 +
        unitMarkerMeasure marker +
        identifierMeasure name +
        expressionListOptionMeasure arguments
  | .proxy marker typeExpression =>
      1 + unitMarkerMeasure marker + typeExprMeasure typeExpression
  | .literal literal =>
      1 + literalMeasure literal
  | .lambda parameters returnType body =>
      1 +
        measureList parameterMeasure parameters +
        measureOption typeExprMeasure returnType +
        bodyMeasure body
  | .annotation expression typeExpression =>
      1 + expressionMeasure expression + typeExprMeasure typeExpression
  | .keywordConditional condition thenBranch elseBranch =>
      1 +
        expressionMeasure condition +
        expressionMeasure thenBranch +
        expressionMeasure elseBranch
  | .ternaryConditional condition thenBranch elseBranch =>
      1 +
        expressionMeasure condition +
        expressionMeasure thenBranch +
        expressionMeasure elseBranch
  | .index receiver index =>
      1 + expressionMeasure receiver + expressionMeasure index
  | .prefix operator operand =>
      1 + prefixOperatorMeasure operator + expressionMeasure operand
  | .infix operator left right =>
      1 +
        infixOperatorMeasure operator +
        expressionMeasure left +
        expressionMeasure right
  | .tuple elements =>
      1 + expressionListMeasure elements
  | .group inner =>
      1 + expressionMeasure inner

private def patternPayloadMeasure : PatternPayload → Nat
  | .named name arguments =>
      1 + qualifiedNameMeasure name + patternArgumentsMeasure arguments
  | .dotConstructor marker name arguments =>
      1 +
        unitMarkerMeasure marker +
        identifierMeasure name +
        patternArgumentsMeasure arguments
  | .wildcard marker =>
      1 + markerMeasure marker
  | .literal literal =>
      1 + literalMeasure literal
  | .comptime marker expression =>
      1 + markerMeasure marker + expressionMeasure expression
  | .tuple elements =>
      1 + patternListMeasure elements
  | .group inner =>
      1 + patternMeasure inner

private def bodyPayloadMeasure : BodyPayload → Nat
  | ⟨_, statements⟩ =>
      1 + statementListMeasure statements

private def letBindingPayloadMeasure : LetBindingPayload → Nat
  | ⟨comptime, name, typeExpression, initializer⟩ =>
      1 +
        measureOption markerMeasure comptime +
        identifierMeasure name +
        measureOption typeExprMeasure typeExpression +
        expressionOptionMeasure initializer

private def forInitItemPayloadMeasure : ForInitItemPayload → Nat
  | .letBinding binding =>
      1 + letBindingMeasure binding
  | .assignment operator left right =>
      1 +
        assignmentOperatorMeasure operator +
        expressionMeasure left +
        expressionMeasure right
  | .expression expression =>
      1 + expressionMeasure expression

private def forPostItemPayloadMeasure : ForPostItemPayload → Nat
  | .assignment operator left right =>
      1 +
        assignmentOperatorMeasure operator +
        expressionMeasure left +
        expressionMeasure right
  | .expression expression =>
      1 + expressionMeasure expression

private def matchArmPayloadMeasure : MatchArmPayload → Nat
  | ⟨patterns, body⟩ =>
      1 + patternNonemptyMeasure patterns + bodyMeasure body

private def statementPayloadMeasure : StatementPayload → Nat
  | .assignment operator left right =>
      1 +
        assignmentOperatorMeasure operator +
        expressionMeasure left +
        expressionMeasure right
  | .letBinding binding =>
      1 + letBindingMeasure binding
  | .block body =>
      1 + bodyMeasure body
  | .expression expression _ =>
      1 + expressionMeasure expression
  | .return value _ =>
      1 + expressionOptionMeasure value
  | .match scrutinees arms _ =>
      1 +
        expressionNonemptyMeasure scrutinees +
        matchArmNonemptyMeasure arms
  | .assembly slice =>
      1 + assemblySliceMeasure slice
  | .ifThenElse condition thenBody elseBody =>
      1 +
        expressionMeasure condition +
        bodyMeasure thenBody +
        bodyOptionMeasure elseBody
  | .forLoop initializers condition post body =>
      1 +
        forInitItemListMeasure initializers +
        expressionMeasure condition +
        forPostItemListMeasure post +
        bodyMeasure body
  | .break _ =>
      1
  | .continue _ =>
      1

private def expressionMeasure : Expression → Nat
  | ⟨_, payload⟩ =>
      1 + expressionPayloadMeasure payload

private def expressionListMeasure : List Expression → Nat
  | [] => 0
  | head :: tail =>
      expressionMeasure head + expressionListMeasure tail

private def expressionListOptionMeasure : Option (List Expression) → Nat
  | none => 0
  | some expressions => expressionListMeasure expressions

private def bodyMeasure : Body → Nat
  | ⟨_, payload⟩ =>
      1 + bodyPayloadMeasure payload

private def patternArgumentsMeasure :
    Option (NonemptyList Pattern) → Nat
  | none => 0
  | some patterns => patternNonemptyMeasure patterns

private def patternListMeasure : List Pattern → Nat
  | [] => 0
  | head :: tail =>
      patternMeasure head + patternListMeasure tail

private def patternMeasure : Pattern → Nat
  | ⟨_, payload⟩ =>
      1 + patternPayloadMeasure payload

private def statementListMeasure : List Statement → Nat
  | [] => 0
  | head :: tail =>
      statementMeasure head + statementListMeasure tail

private def expressionOptionMeasure : Option Expression → Nat
  | none => 0
  | some expression => expressionMeasure expression

private def letBindingMeasure : LetBinding → Nat
  | ⟨_, payload⟩ =>
      1 + letBindingPayloadMeasure payload

private def patternNonemptyMeasure : NonemptyList Pattern → Nat
  | ⟨head, tail⟩ =>
      patternMeasure head + patternListMeasure tail

private def expressionNonemptyMeasure : NonemptyList Expression → Nat
  | ⟨head, tail⟩ =>
      expressionMeasure head + expressionListMeasure tail

private def matchArmNonemptyMeasure : NonemptyList MatchArm → Nat
  | ⟨head, tail⟩ =>
      matchArmMeasure head + matchArmListMeasure tail

private def bodyOptionMeasure : Option Body → Nat
  | none => 0
  | some body => bodyMeasure body

private def forInitItemListMeasure : List ForInitItem → Nat
  | [] => 0
  | head :: tail =>
      forInitItemMeasure head + forInitItemListMeasure tail

private def forPostItemListMeasure : List ForPostItem → Nat
  | [] => 0
  | head :: tail =>
      forPostItemMeasure head + forPostItemListMeasure tail

private def statementMeasure : Statement → Nat
  | ⟨_, payload⟩ =>
      1 + statementPayloadMeasure payload

private def matchArmMeasure : MatchArm → Nat
  | ⟨_, payload⟩ =>
      1 + matchArmPayloadMeasure payload

private def matchArmListMeasure : List MatchArm → Nat
  | [] => 0
  | head :: tail =>
      matchArmMeasure head + matchArmListMeasure tail

private def forInitItemMeasure : ForInitItem → Nat
  | ⟨_, payload⟩ =>
      1 + forInitItemPayloadMeasure payload

private def forPostItemMeasure : ForPostItem → Nat
  | ⟨_, payload⟩ =>
      1 + forPostItemPayloadMeasure payload

end

private def classMethodDeclMeasure
    (declaration : ClassMethodDecl) : Nat :=
  2 + functionSignatureMeasure declaration.payload.signature

private def functionDeclMeasure (declaration : FunctionDecl) : Nat :=
  2 +
    functionSignatureMeasure declaration.payload.signature +
    bodyMeasure declaration.payload.body

private def fallbackDeclMeasure (declaration : FallbackDecl) : Nat :=
  2 +
    measureOption genericPrefixMeasure declaration.payload.genericPrefix +
    measureOption markerMeasure declaration.payload.public +
    measureOption markerMeasure declaration.payload.payable +
    markerMeasure declaration.payload.marker +
    measureList parameterMeasure declaration.payload.parameters +
    measureOption typeExprMeasure declaration.payload.returnType +
    bodyMeasure declaration.payload.body

private def contractConstructorDeclMeasure
    (declaration : ContractConstructorDecl) : Nat :=
  2 +
    measureOption markerMeasure declaration.payload.public +
    measureOption markerMeasure declaration.payload.payable +
    markerMeasure declaration.payload.marker +
    measureList parameterMeasure declaration.payload.parameters +
    bodyMeasure declaration.payload.body

private def dataConstructorMeasure
    (dataConstructor : DataConstructor) : Nat :=
  2 +
    identifierMeasure dataConstructor.payload.name +
    measureOption
      (measureNonemptyList typeExprMeasure)
      dataConstructor.payload.fields

private def dataDeclMeasure (declaration : DataDecl) : Nat :=
  2 +
    identifierMeasure declaration.payload.name +
    measureOption
      (measureNonemptyList identifierMeasure)
      declaration.payload.parameters +
    measureOption
      (measureNonemptyList dataConstructorMeasure)
      declaration.payload.constructors

private def typeAliasDeclMeasure (declaration : TypeAliasDecl) : Nat :=
  2 +
    identifierMeasure declaration.payload.name +
    measureOption
      (measureNonemptyList identifierMeasure)
      declaration.payload.parameters +
    typeExprMeasure declaration.payload.body

private def classDeclMeasure (declaration : ClassDecl) : Nat :=
  2 +
    measureOption genericPrefixMeasure declaration.payload.genericPrefix +
    typeExprMeasure declaration.payload.main +
    identifierMeasure declaration.payload.className +
    measureOption
      (measureNonemptyList typeExprMeasure)
      declaration.payload.parameters +
    measureList classMethodDeclMeasure declaration.payload.methods

private def instanceDeclMeasure (declaration : InstanceDecl) : Nat :=
  2 +
    measureOption genericPrefixMeasure declaration.payload.genericPrefix +
    measureOption markerMeasure declaration.payload.default +
    typeExprMeasure declaration.payload.main +
    qualifiedNameMeasure declaration.payload.className +
    measureOption
      (measureNonemptyList typeExprMeasure)
      declaration.payload.parameters +
    measureList functionDeclMeasure declaration.payload.methods

private def pragmaDeclMeasure (declaration : PragmaDecl) : Nat :=
  2 +
    pragmaKindMeasure declaration.payload.kind +
    measureList identifierMeasure declaration.payload.targets

private def fieldDeclMeasure (declaration : FieldDecl) : Nat :=
  2 +
    identifierMeasure declaration.payload.name +
    typeExprMeasure declaration.payload.type +
    measureOption expressionMeasure declaration.payload.initializer

private def contractMemberMeasure (member : ContractMember) : Nat :=
  2 +
    match member.payload with
    | .dataDecl declaration => dataDeclMeasure declaration
    | .typeAlias declaration => typeAliasDeclMeasure declaration
    | .field declaration => fieldDeclMeasure declaration
    | .function declaration => functionDeclMeasure declaration
    | .fallback declaration => fallbackDeclMeasure declaration
    | .constructor declaration =>
        contractConstructorDeclMeasure declaration

private def contractDeclMeasure (declaration : ContractDecl) : Nat :=
  2 +
    identifierMeasure declaration.payload.name +
    measureOption
      (measureNonemptyList identifierMeasure)
      declaration.payload.parameters +
    measureList contractMemberMeasure declaration.payload.members

private def topItemMeasure (item : TopItem) : Nat :=
  2 +
    match item.payload with
    | .importDecl declaration => importDeclMeasure declaration
    | .exportDecl declaration => exportModeMeasure declaration
    | .pragmaDecl declaration => pragmaDeclMeasure declaration
    | .dataDecl declaration => dataDeclMeasure declaration
    | .typeAliasDecl declaration => typeAliasDeclMeasure declaration
    | .classDecl declaration => classDeclMeasure declaration
    | .instanceDecl declaration => instanceDeclMeasure declaration
    | .contractDecl declaration => contractDeclMeasure declaration
    | .functionDecl declaration => functionDeclMeasure declaration

/-- Count every concrete located wrapper and payload carrier in a parsed module. -/
def astNodeMeasure (parsedModule : ParsedModuleV1) : Nat :=
  2 + measureList topItemMeasure parsedModule.payload.items

namespace StructureFuelDepth

/-- One AST carrier visited by the mutually recursive structural collectors. -/
inductive RecursiveAstNode where
  | expression (value : Expression)
  | pattern (value : Pattern)
  | body (loopDepth : Nat) (value : Body)
  | statement (loopDepth : Nat) (value : Statement)
  | forInit (value : ForInitItem)
  | forPost (value : ForPostItem)

/-- A collector entry point reached without consuming structural fuel. -/
inductive RecursiveAstRoot
    (module : ParsedModuleV1) : RecursiveAstNode → Prop where
  | topLevelFunction
      {itemSpan : SourceSpan}
      {declaration : FunctionDecl}
      (member :
        (⟨itemSpan, .functionDecl declaration⟩ : TopItem) ∈
          module.payload.items) :
      RecursiveAstRoot module (.body 0 declaration.payload.body)
  | instanceMethod
      {itemSpan : SourceSpan}
      {declaration : InstanceDecl}
      {method : FunctionDecl}
      (itemMember :
        (⟨itemSpan, .instanceDecl declaration⟩ : TopItem) ∈
          module.payload.items)
      (methodMember : method ∈ declaration.payload.methods) :
      RecursiveAstRoot module (.body 0 method.payload.body)
  | contractFieldInitializer
      {itemSpan : SourceSpan}
      {declaration : ContractDecl}
      {memberSpan : SourceSpan}
      {field : FieldDecl}
      {initializer : Expression}
      (itemMember :
        (⟨itemSpan, .contractDecl declaration⟩ : TopItem) ∈
          module.payload.items)
      (memberMember :
        (⟨memberSpan, .field field⟩ : ContractMember) ∈
          declaration.payload.members)
      (initializer_eq : field.payload.initializer = some initializer) :
      RecursiveAstRoot module (.expression initializer)
  | contractFunction
      {itemSpan : SourceSpan}
      {declaration : ContractDecl}
      {memberSpan : SourceSpan}
      {functionDeclaration : FunctionDecl}
      (itemMember :
        (⟨itemSpan, .contractDecl declaration⟩ : TopItem) ∈
          module.payload.items)
      (memberMember :
        (⟨memberSpan, .function functionDeclaration⟩ : ContractMember) ∈
          declaration.payload.members) :
      RecursiveAstRoot module (.body 0 functionDeclaration.payload.body)
  | fallback
      {itemSpan : SourceSpan}
      {declaration : ContractDecl}
      {memberSpan : SourceSpan}
      {fallbackDeclaration : FallbackDecl}
      (itemMember :
        (⟨itemSpan, .contractDecl declaration⟩ : TopItem) ∈
          module.payload.items)
      (memberMember :
        (⟨memberSpan, .fallback fallbackDeclaration⟩ : ContractMember) ∈
          declaration.payload.members) :
      RecursiveAstRoot module (.body 0 fallbackDeclaration.payload.body)
  | constructor
      {itemSpan : SourceSpan}
      {declaration : ContractDecl}
      {memberSpan : SourceSpan}
      {constructorDeclaration : ContractConstructorDecl}
      (itemMember :
        (⟨itemSpan, .contractDecl declaration⟩ : TopItem) ∈
          module.payload.items)
      (memberMember :
        (⟨memberSpan, .constructor constructorDeclaration⟩ : ContractMember) ∈
          declaration.payload.members) :
      RecursiveAstRoot module (.body 0 constructorDeclaration.payload.body)

/-- One fuel-consuming recursive call made by a structural collector. -/
inductive RecursiveAstChild : RecursiveAstNode → RecursiveAstNode → Prop where
  | expressionCallCallee
      {span : SourceSpan} {callee : Expression} {arguments : List Expression} :
      RecursiveAstChild
        (.expression ⟨span, .call callee arguments⟩)
        (.expression callee)
  | expressionCallArgument
      {span : SourceSpan} {callee argument : Expression}
      {arguments : List Expression}
      (member : argument ∈ arguments) :
      RecursiveAstChild
        (.expression ⟨span, .call callee arguments⟩)
        (.expression argument)
  | expressionSelectReceiver
      {span : SourceSpan} {receiver : Expression}
      {field : IdentifierOccurrence} :
      RecursiveAstChild
        (.expression ⟨span, .select receiver field⟩)
        (.expression receiver)
  | expressionDotConstructorArgument
      {span : SourceSpan} {marker : Located Unit}
      {name : IdentifierOccurrence} {arguments : List Expression}
      {argument : Expression}
      (member : argument ∈ arguments) :
      RecursiveAstChild
        (.expression ⟨span, .dotConstructor marker name (some arguments)⟩)
        (.expression argument)
  | expressionLambdaBody
      {span : SourceSpan} {parameters : List Parameter}
      {returnType : Option TypeExpr} {body : Body} :
      RecursiveAstChild
        (.expression ⟨span, .lambda parameters returnType body⟩)
        (.body 0 body)
  | expressionAnnotationInner
      {span : SourceSpan} {inner : Expression} {typeExpression : TypeExpr} :
      RecursiveAstChild
        (.expression ⟨span, .annotation inner typeExpression⟩)
        (.expression inner)
  | expressionKeywordCondition
      {span : SourceSpan} {condition thenBranch elseBranch : Expression} :
      RecursiveAstChild
        (.expression
          ⟨span, .keywordConditional condition thenBranch elseBranch⟩)
        (.expression condition)
  | expressionKeywordThen
      {span : SourceSpan} {condition thenBranch elseBranch : Expression} :
      RecursiveAstChild
        (.expression
          ⟨span, .keywordConditional condition thenBranch elseBranch⟩)
        (.expression thenBranch)
  | expressionKeywordElse
      {span : SourceSpan} {condition thenBranch elseBranch : Expression} :
      RecursiveAstChild
        (.expression
          ⟨span, .keywordConditional condition thenBranch elseBranch⟩)
        (.expression elseBranch)
  | expressionTernaryCondition
      {span : SourceSpan} {condition thenBranch elseBranch : Expression} :
      RecursiveAstChild
        (.expression
          ⟨span, .ternaryConditional condition thenBranch elseBranch⟩)
        (.expression condition)
  | expressionTernaryThen
      {span : SourceSpan} {condition thenBranch elseBranch : Expression} :
      RecursiveAstChild
        (.expression
          ⟨span, .ternaryConditional condition thenBranch elseBranch⟩)
        (.expression thenBranch)
  | expressionTernaryElse
      {span : SourceSpan} {condition thenBranch elseBranch : Expression} :
      RecursiveAstChild
        (.expression
          ⟨span, .ternaryConditional condition thenBranch elseBranch⟩)
        (.expression elseBranch)
  | expressionIndexReceiver
      {span : SourceSpan} {receiver index : Expression} :
      RecursiveAstChild
        (.expression ⟨span, .index receiver index⟩)
        (.expression receiver)
  | expressionIndex
      {span : SourceSpan} {receiver index : Expression} :
      RecursiveAstChild
        (.expression ⟨span, .index receiver index⟩)
        (.expression index)
  | expressionPrefixOperand
      {span : SourceSpan} {operator : Located PrefixOperator}
      {operand : Expression} :
      RecursiveAstChild
        (.expression ⟨span, .prefix operator operand⟩)
        (.expression operand)
  | expressionInfixLeft
      {span : SourceSpan} {operator : Located InfixOperator}
      {left right : Expression} :
      RecursiveAstChild
        (.expression ⟨span, .infix operator left right⟩)
        (.expression left)
  | expressionInfixRight
      {span : SourceSpan} {operator : Located InfixOperator}
      {left right : Expression} :
      RecursiveAstChild
        (.expression ⟨span, .infix operator left right⟩)
        (.expression right)
  | expressionTupleElement
      {span : SourceSpan} {elements : List Expression} {element : Expression}
      (member : element ∈ elements) :
      RecursiveAstChild
        (.expression ⟨span, .tuple elements⟩)
        (.expression element)
  | expressionGroupInner
      {span : SourceSpan} {inner : Expression} :
      RecursiveAstChild
        (.expression ⟨span, .group inner⟩)
        (.expression inner)
  | patternNamedArgument
      {span : SourceSpan} {name : QualifiedName}
      {arguments : NonemptyList Pattern} {argument : Pattern}
      (member : argument ∈ arguments.head :: arguments.tail) :
      RecursiveAstChild
        (.pattern ⟨span, .named name (some arguments)⟩)
        (.pattern argument)
  | patternDotConstructorArgument
      {span : SourceSpan} {marker : Located Unit}
      {name : IdentifierOccurrence} {arguments : NonemptyList Pattern}
      {argument : Pattern}
      (member : argument ∈ arguments.head :: arguments.tail) :
      RecursiveAstChild
        (.pattern ⟨span, .dotConstructor marker name (some arguments)⟩)
        (.pattern argument)
  | patternComptimeExpression
      {span : SourceSpan} {marker : Marker} {expression : Expression} :
      RecursiveAstChild
        (.pattern ⟨span, .comptime marker expression⟩)
        (.expression expression)
  | patternTupleElement
      {span : SourceSpan} {elements : List Pattern} {element : Pattern}
      (member : element ∈ elements) :
      RecursiveAstChild
        (.pattern ⟨span, .tuple elements⟩)
        (.pattern element)
  | patternGroupInner
      {span : SourceSpan} {inner : Pattern} :
      RecursiveAstChild
        (.pattern ⟨span, .group inner⟩)
        (.pattern inner)
  | bodyStatement
      {loopDepth : Nat} {span : SourceSpan} {origin : BodyOrigin}
      {statements : List Statement} {statement : Statement}
      (member : statement ∈ statements) :
      RecursiveAstChild
        (.body loopDepth ⟨span, ⟨origin, statements⟩⟩)
        (.statement loopDepth statement)
  | statementAssignmentLeft
      {loopDepth : Nat} {span : SourceSpan}
      {operator : Located AssignmentOperator}
      {left right : Expression} :
      RecursiveAstChild
        (.statement loopDepth ⟨span, .assignment operator left right⟩)
        (.expression left)
  | statementAssignmentRight
      {loopDepth : Nat} {span : SourceSpan}
      {operator : Located AssignmentOperator}
      {left right : Expression} :
      RecursiveAstChild
        (.statement loopDepth ⟨span, .assignment operator left right⟩)
        (.expression right)
  | statementLetInitializer
      {loopDepth : Nat} {span : SourceSpan}
      {binding : LetBinding} {initializer : Expression}
      (initializer_eq : binding.payload.initializer = some initializer) :
      RecursiveAstChild
        (.statement loopDepth ⟨span, .letBinding binding⟩)
        (.expression initializer)
  | statementBlockBody
      {loopDepth : Nat} {span : SourceSpan} {body : Body} :
      RecursiveAstChild
        (.statement loopDepth ⟨span, .block body⟩)
        (.body loopDepth body)
  | statementExpression
      {loopDepth : Nat} {span : SourceSpan} {expression : Expression}
      {terminator : Option SourceSpan} :
      RecursiveAstChild
        (.statement loopDepth ⟨span, .expression expression terminator⟩)
        (.expression expression)
  | statementReturnExpression
      {loopDepth : Nat} {span : SourceSpan}
      {expression : Expression} {terminator : SourceSpan} :
      RecursiveAstChild
        (.statement loopDepth ⟨span, .return (some expression) terminator⟩)
        (.expression expression)
  | statementMatchScrutinee
      {loopDepth : Nat} {span : SourceSpan}
      {scrutinees : NonemptyList Expression}
      {arms : NonemptyList MatchArm} {terminator : Option SourceSpan}
      {scrutinee : Expression}
      (member : scrutinee ∈ scrutinees.head :: scrutinees.tail) :
      RecursiveAstChild
        (.statement loopDepth ⟨span, .match scrutinees arms terminator⟩)
        (.expression scrutinee)
  | statementMatchPattern
      {loopDepth : Nat} {span : SourceSpan}
      {scrutinees : NonemptyList Expression}
      {arms : NonemptyList MatchArm} {terminator : Option SourceSpan}
      {arm : MatchArm} {pattern : Pattern}
      (armMember : arm ∈ arms.head :: arms.tail)
      (patternMember :
        pattern ∈ arm.payload.patterns.head :: arm.payload.patterns.tail) :
      RecursiveAstChild
        (.statement loopDepth ⟨span, .match scrutinees arms terminator⟩)
        (.pattern pattern)
  | statementMatchBody
      {loopDepth : Nat} {span : SourceSpan}
      {scrutinees : NonemptyList Expression}
      {arms : NonemptyList MatchArm} {terminator : Option SourceSpan}
      {arm : MatchArm}
      (armMember : arm ∈ arms.head :: arms.tail) :
      RecursiveAstChild
        (.statement loopDepth ⟨span, .match scrutinees arms terminator⟩)
        (.body loopDepth arm.payload.body)
  | statementIfCondition
      {loopDepth : Nat} {span : SourceSpan} {condition : Expression}
      {thenBody : Body} {elseBody : Option Body} :
      RecursiveAstChild
        (.statement loopDepth
          ⟨span, .ifThenElse condition thenBody elseBody⟩)
        (.expression condition)
  | statementIfThenBody
      {loopDepth : Nat} {span : SourceSpan} {condition : Expression}
      {thenBody : Body} {elseBody : Option Body} :
      RecursiveAstChild
        (.statement loopDepth
          ⟨span, .ifThenElse condition thenBody elseBody⟩)
        (.body loopDepth thenBody)
  | statementIfElseBody
      {loopDepth : Nat} {span : SourceSpan} {condition : Expression}
      {thenBody elseBody : Body} :
      RecursiveAstChild
        (.statement loopDepth
          ⟨span, .ifThenElse condition thenBody (some elseBody)⟩)
        (.body loopDepth elseBody)
  | statementForInitializer
      {loopDepth : Nat} {span : SourceSpan}
      {initializers : List ForInitItem}
      {condition : Expression} {post : List ForPostItem} {body : Body}
      {initializer : ForInitItem}
      (member : initializer ∈ initializers) :
      RecursiveAstChild
        (.statement loopDepth
          ⟨span, .forLoop initializers condition post body⟩)
        (.forInit initializer)
  | statementForCondition
      {loopDepth : Nat} {span : SourceSpan}
      {initializers : List ForInitItem}
      {condition : Expression} {post : List ForPostItem} {body : Body} :
      RecursiveAstChild
        (.statement loopDepth
          ⟨span, .forLoop initializers condition post body⟩)
        (.expression condition)
  | statementForPost
      {loopDepth : Nat} {span : SourceSpan}
      {initializers : List ForInitItem}
      {condition : Expression} {post : List ForPostItem} {body : Body}
      {item : ForPostItem}
      (member : item ∈ post) :
      RecursiveAstChild
        (.statement loopDepth
          ⟨span, .forLoop initializers condition post body⟩)
        (.forPost item)
  | statementForBody
      {loopDepth : Nat} {span : SourceSpan}
      {initializers : List ForInitItem}
      {condition : Expression} {post : List ForPostItem} {body : Body} :
      RecursiveAstChild
        (.statement loopDepth
          ⟨span, .forLoop initializers condition post body⟩)
        (.body (loopDepth + 1) body)
  | forInitLetInitializer
      {span : SourceSpan} {binding : LetBinding} {initializer : Expression}
      (initializer_eq : binding.payload.initializer = some initializer) :
      RecursiveAstChild
        (.forInit ⟨span, .letBinding binding⟩)
        (.expression initializer)
  | forInitAssignmentLeft
      {span : SourceSpan} {operator : Located AssignmentOperator}
      {left right : Expression} :
      RecursiveAstChild
        (.forInit ⟨span, .assignment operator left right⟩)
        (.expression left)
  | forInitAssignmentRight
      {span : SourceSpan} {operator : Located AssignmentOperator}
      {left right : Expression} :
      RecursiveAstChild
        (.forInit ⟨span, .assignment operator left right⟩)
        (.expression right)
  | forInitExpression
      {span : SourceSpan} {expression : Expression} :
      RecursiveAstChild
        (.forInit ⟨span, .expression expression⟩)
        (.expression expression)
  | forPostAssignmentLeft
      {span : SourceSpan} {operator : Located AssignmentOperator}
      {left right : Expression} :
      RecursiveAstChild
        (.forPost ⟨span, .assignment operator left right⟩)
        (.expression left)
  | forPostAssignmentRight
      {span : SourceSpan} {operator : Located AssignmentOperator}
      {left right : Expression} :
      RecursiveAstChild
        (.forPost ⟨span, .assignment operator left right⟩)
        (.expression right)
  | forPostExpression
      {span : SourceSpan} {expression : Expression} :
      RecursiveAstChild
        (.forPost ⟨span, .expression expression⟩)
        (.expression expression)

/-- A recursive collector node reached from a module at an exact fuel depth. -/
inductive StructuralFuelPath
    (module : ParsedModuleV1) : RecursiveAstNode → Nat → Prop where
  | root {node : RecursiveAstNode} :
      RecursiveAstRoot module node → StructuralFuelPath module node 0
  | child {parent child : RecursiveAstNode} {depth : Nat} :
      StructuralFuelPath module parent depth →
      RecursiveAstChild parent child →
      StructuralFuelPath module child (depth + 1)

private def recursiveAstNodeMeasure : RecursiveAstNode → Nat
  | .expression value => expressionMeasure value
  | .pattern value => patternMeasure value
  | .body _ value => bodyMeasure value
  | .statement _ value => statementMeasure value
  | .forInit value => forInitItemMeasure value
  | .forPost value => forPostItemMeasure value

private theorem measure_le_measureList_of_mem
    {α : Type} (measure : α → Nat) {value : α} {values : List α}
    (member : value ∈ values) : measure value ≤ measureList measure values := by
  induction values with
  | nil => simp at member
  | cons head tail induction =>
      simp only [List.mem_cons] at member
      simp only [measureList, List.map_cons, List.sum_cons]
      rcases member with rfl | member
      · omega
      · have bound := induction member
        simp only [measureList] at bound
        omega

private theorem expressionListMeasure_eq_measureList
    (values : List Expression) :
    expressionListMeasure values = measureList expressionMeasure values := by
  induction values with
  | nil => rfl
  | cons head tail induction =>
      simp [expressionListMeasure, measureList, induction]

private theorem patternListMeasure_eq_measureList
    (values : List Pattern) :
    patternListMeasure values = measureList patternMeasure values := by
  induction values with
  | nil => rfl
  | cons head tail induction =>
      simp [patternListMeasure, measureList, induction]

private theorem statementListMeasure_eq_measureList
    (values : List Statement) :
    statementListMeasure values = measureList statementMeasure values := by
  induction values with
  | nil => rfl
  | cons head tail induction =>
      simp [statementListMeasure, measureList, induction]

private theorem forInitItemListMeasure_eq_measureList
    (values : List ForInitItem) :
    forInitItemListMeasure values = measureList forInitItemMeasure values := by
  induction values with
  | nil => rfl
  | cons head tail induction =>
      simp [forInitItemListMeasure, measureList, induction]

private theorem forPostItemListMeasure_eq_measureList
    (values : List ForPostItem) :
    forPostItemListMeasure values = measureList forPostItemMeasure values := by
  induction values with
  | nil => rfl
  | cons head tail induction =>
      simp [forPostItemListMeasure, measureList, induction]

private theorem matchArmListMeasure_eq_measureList
    (values : List MatchArm) :
    matchArmListMeasure values = measureList matchArmMeasure values := by
  induction values with
  | nil => rfl
  | cons head tail induction =>
      simp [matchArmListMeasure, measureList, induction]

private theorem expressionMeasure_le_expressionListMeasure_of_mem
    {value : Expression} {values : List Expression}
    (member : value ∈ values) :
    expressionMeasure value ≤ expressionListMeasure values := by
  rw [expressionListMeasure_eq_measureList]
  exact measure_le_measureList_of_mem expressionMeasure member

private theorem patternMeasure_le_patternListMeasure_of_mem
    {value : Pattern} {values : List Pattern}
    (member : value ∈ values) :
    patternMeasure value ≤ patternListMeasure values := by
  rw [patternListMeasure_eq_measureList]
  exact measure_le_measureList_of_mem patternMeasure member

private theorem statementMeasure_le_statementListMeasure_of_mem
    {value : Statement} {values : List Statement}
    (member : value ∈ values) :
    statementMeasure value ≤ statementListMeasure values := by
  rw [statementListMeasure_eq_measureList]
  exact measure_le_measureList_of_mem statementMeasure member

private theorem forInitItemMeasure_le_forInitItemListMeasure_of_mem
    {value : ForInitItem} {values : List ForInitItem}
    (member : value ∈ values) :
    forInitItemMeasure value ≤ forInitItemListMeasure values := by
  rw [forInitItemListMeasure_eq_measureList]
  exact measure_le_measureList_of_mem forInitItemMeasure member

private theorem forPostItemMeasure_le_forPostItemListMeasure_of_mem
    {value : ForPostItem} {values : List ForPostItem}
    (member : value ∈ values) :
    forPostItemMeasure value ≤ forPostItemListMeasure values := by
  rw [forPostItemListMeasure_eq_measureList]
  exact measure_le_measureList_of_mem forPostItemMeasure member

private theorem matchArmMeasure_le_matchArmListMeasure_of_mem
    {value : MatchArm} {values : List MatchArm}
    (member : value ∈ values) :
    matchArmMeasure value ≤ matchArmListMeasure values := by
  rw [matchArmListMeasure_eq_measureList]
  exact measure_le_measureList_of_mem matchArmMeasure member

private theorem expressionMeasure_le_expressionNonemptyMeasure_of_mem
    {value : Expression} {values : NonemptyList Expression}
    (member : value ∈ values.head :: values.tail) :
    expressionMeasure value ≤ expressionNonemptyMeasure values := by
  cases values with
  | mk head tail =>
      simp only at member ⊢
      rw [expressionNonemptyMeasure]
      rcases List.mem_cons.mp member with rfl | member
      · omega
      · have bound :=
          expressionMeasure_le_expressionListMeasure_of_mem member
        omega

private theorem patternMeasure_le_patternNonemptyMeasure_of_mem
    {value : Pattern} {values : NonemptyList Pattern}
    (member : value ∈ values.head :: values.tail) :
    patternMeasure value ≤ patternNonemptyMeasure values := by
  cases values with
  | mk head tail =>
      simp only at member ⊢
      rw [patternNonemptyMeasure]
      rcases List.mem_cons.mp member with rfl | member
      · omega
      · have bound := patternMeasure_le_patternListMeasure_of_mem member
        omega

private theorem matchArmMeasure_le_matchArmNonemptyMeasure_of_mem
    {value : MatchArm} {values : NonemptyList MatchArm}
    (member : value ∈ values.head :: values.tail) :
    matchArmMeasure value ≤ matchArmNonemptyMeasure values := by
  cases values with
  | mk head tail =>
      simp only at member ⊢
      rw [matchArmNonemptyMeasure]
      rcases List.mem_cons.mp member with rfl | member
      · omega
      · have bound := matchArmMeasure_le_matchArmListMeasure_of_mem member
        omega

private theorem expressionMeasure_le_letBindingMeasure_of_initializer
    {binding : LetBinding} {initializer : Expression}
    (initializer_eq : binding.payload.initializer = some initializer) :
    expressionMeasure initializer ≤ letBindingMeasure binding := by
  cases binding with
  | mk span payload =>
      cases payload with
      | mk comptime name typeExpression initializerOption =>
          simp only at initializer_eq ⊢
          simp [letBindingMeasure, letBindingPayloadMeasure,
            initializer_eq, expressionOptionMeasure]
          omega

private theorem patternMeasure_le_matchArmNonemptyMeasure_of_mem
    {pattern : Pattern} {arm : MatchArm} {arms : NonemptyList MatchArm}
    (armMember : arm ∈ arms.head :: arms.tail)
    (patternMember :
      pattern ∈ arm.payload.patterns.head :: arm.payload.patterns.tail) :
    patternMeasure pattern ≤ matchArmNonemptyMeasure arms := by
  cases arm with
  | mk span payload =>
      cases payload with
      | mk patterns body =>
          simp only at armMember patternMember ⊢
          have patternBound :=
            patternMeasure_le_patternNonemptyMeasure_of_mem patternMember
          have armBound :=
            matchArmMeasure_le_matchArmNonemptyMeasure_of_mem armMember
          simp only [matchArmMeasure, matchArmPayloadMeasure] at armBound
          omega

private theorem bodyMeasure_le_matchArmNonemptyMeasure_of_mem
    {arm : MatchArm} {arms : NonemptyList MatchArm}
    (armMember : arm ∈ arms.head :: arms.tail) :
    bodyMeasure arm.payload.body ≤ matchArmNonemptyMeasure arms := by
  cases arm with
  | mk span payload =>
      cases payload with
      | mk patterns body =>
          simp only at armMember ⊢
          have armBound :=
            matchArmMeasure_le_matchArmNonemptyMeasure_of_mem armMember
          simp only [matchArmMeasure, matchArmPayloadMeasure] at armBound
          omega

private theorem RecursiveAstChild.measure_add_one_le
    {parent child : RecursiveAstNode}
    (edge : RecursiveAstChild parent child) :
    recursiveAstNodeMeasure child + 1 ≤ recursiveAstNodeMeasure parent := by
  cases edge
  all_goals
    try
      have expressionListBound :=
        expressionMeasure_le_expressionListMeasure_of_mem (by assumption)
    try
      have patternListBound :=
        patternMeasure_le_patternListMeasure_of_mem (by assumption)
    try
      have statementListBound :=
        statementMeasure_le_statementListMeasure_of_mem (by assumption)
    try
      have forInitListBound :=
        forInitItemMeasure_le_forInitItemListMeasure_of_mem (by assumption)
    try
      have forPostListBound :=
        forPostItemMeasure_le_forPostItemListMeasure_of_mem (by assumption)
    try
      have expressionNonemptyBound :=
        expressionMeasure_le_expressionNonemptyMeasure_of_mem (by assumption)
    try
      have patternNonemptyBound :=
        patternMeasure_le_patternNonemptyMeasure_of_mem (by assumption)
    try
      have letInitializerBound :=
        expressionMeasure_le_letBindingMeasure_of_initializer (by assumption)
    try
      have matchPatternBound :=
        patternMeasure_le_matchArmNonemptyMeasure_of_mem
          (by assumption) (by assumption)
    try
      have matchBodyBound :=
        bodyMeasure_le_matchArmNonemptyMeasure_of_mem (by assumption)
  all_goals
    simp_all only [
      recursiveAstNodeMeasure,
      expressionMeasure,
      expressionPayloadMeasure,
      expressionListOptionMeasure,
      patternMeasure,
      patternPayloadMeasure,
      patternArgumentsMeasure,
      bodyMeasure,
      bodyPayloadMeasure,
      statementMeasure,
      statementPayloadMeasure,
      expressionOptionMeasure,
      bodyOptionMeasure,
      forInitItemMeasure,
      forInitItemPayloadMeasure,
      forPostItemMeasure,
      forPostItemPayloadMeasure]
  all_goals omega

private theorem RecursiveAstRoot.measure_lt_astNodeMeasure
    {module : ParsedModuleV1} {node : RecursiveAstNode}
    (root : RecursiveAstRoot module node) :
    recursiveAstNodeMeasure node < astNodeMeasure module := by
  cases root
  all_goals
    have topItemBound :=
      measure_le_measureList_of_mem topItemMeasure (by assumption)
    try
      have functionBound :=
        measure_le_measureList_of_mem functionDeclMeasure (by assumption)
    try
      have contractMemberBound :=
        measure_le_measureList_of_mem contractMemberMeasure (by assumption)
  all_goals
    simp_all only [
      recursiveAstNodeMeasure,
      astNodeMeasure,
      topItemMeasure,
      instanceDeclMeasure,
      contractDeclMeasure,
      contractMemberMeasure,
      functionDeclMeasure,
      fieldDeclMeasure,
      fallbackDeclMeasure,
      contractConstructorDeclMeasure,
      measureOption]
  all_goals omega

private theorem StructuralFuelPath.depth_add_measure_lt
    {module : ParsedModuleV1} {node : RecursiveAstNode} {depth : Nat}
    (path : StructuralFuelPath module node depth) :
    depth + recursiveAstNodeMeasure node < astNodeMeasure module := by
  induction path with
  | root root =>
      simpa using root.measure_lt_astNodeMeasure
  | child path edge induction =>
      have decrease := edge.measure_add_one_le
      omega

/-- A structural collector path is shorter than its module-wide fuel bound. -/
theorem StructuralFuelPath.depth_lt_astNodeMeasure
    {module : ParsedModuleV1} {node : RecursiveAstNode} {depth : Nat}
    (path : StructuralFuelPath module node depth) :
    depth < astNodeMeasure module := by
  have invariant := path.depth_add_measure_lt
  omega

end StructureFuelDepth

end Solcore.Surface.Multi
