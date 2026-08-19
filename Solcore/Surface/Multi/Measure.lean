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

end Solcore.Surface.Multi
