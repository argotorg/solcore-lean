import Solcore.Surface.Multi.Token

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Solcore.Workspace

/-- A nonempty list represented by its first element and remaining elements. -/
structure NonemptyList (α : Type) where
  head : α
  tail : List α
  deriving Repr, BEq, DecidableEq

namespace NonemptyList

/-- Map a function over a nonempty list while preserving its shape. -/
def map {α β : Type} (function : α → β)
    (values : NonemptyList α) : NonemptyList β := {
  head := function values.head
  tail := values.tail.map function
}

end NonemptyList

/-- One source-located identifier occurrence. -/
abbrev IdentifierOccurrence := Located Identifier

/-- One source-located module-path component. -/
abbrev PathComponent := Located PathSegment

/-- The payload of a source-preserving qualified name. -/
structure QualifiedNamePayload where
  components : NonemptyList IdentifierOccurrence
  deriving Repr, BEq, DecidableEq

/-- A source-preserving qualified name. -/
abbrev QualifiedName := Located QualifiedNamePayload

/-- The closed set of syntax markers retained as AST leaves. -/
inductive SyntaxMarker where
  | libraryRoot
  | standardRoot
  | externalSigil
  | wildcard
  | fallbackName
  | contractConstructorName
  | publicModifier
  | payableModifier
  | comptimeModifier
  | defaultModifier
  deriving Repr, BEq, DecidableEq

/-- One source-located syntax marker. -/
abbrev Marker := Located SyntaxMarker

/-- A module reference retaining its written root and components. -/
inductive ModuleReferencePayload where
  | relative (components : NonemptyList PathComponent)
  | libraryRoot (marker : Marker) (tail : NonemptyList PathComponent)
  | standard (marker : Marker) (tail : List PathComponent)
  | external
      («at» : Marker)
      (library : Located ExternalLibraryName)
      (tail : NonemptyList PathComponent)
  deriving Repr, BEq, DecidableEq

/-- A source-located module reference. -/
abbrev ModuleReference := Located ModuleReferencePayload

/-- A module-reference spelling with every source location erased. -/
inductive ModuleReferenceShape where
  | relative (components : NonemptyList PathSegment)
  | libraryRoot (tail : NonemptyList PathSegment)
  | standard (tail : List PathSegment)
  | external
      (library : ExternalLibraryName)
      (tail : NonemptyList PathSegment)
  deriving Repr, BEq, DecidableEq

namespace ModuleReference

/-- Erase locations and constructor-determined markers from a module reference. -/
def eraseLocations (reference : ModuleReference) : ModuleReferenceShape :=
  match reference.payload with
  | .relative components =>
      .relative (components.map (·.payload))
  | .libraryRoot _ tail =>
      .libraryRoot (tail.map (·.payload))
  | .standard _ tail =>
      .standard (tail.map (·.payload))
  | .external _ library tail =>
      .external library.payload (tail.map (·.payload))

end ModuleReference

/-- One entry in an import selector. -/
inductive ImportSelectorEntryPayload where
  | wildcard (marker : Marker)
  | named
      (source : IdentifierOccurrence)
      (alias : Option IdentifierOccurrence)
  deriving Repr, BEq, DecidableEq

/-- A source-located import-selector entry. -/
abbrev ImportSelectorEntry := Located ImportSelectorEntryPayload

/-- The raw finite entries of one import selection. -/
structure ImportSelectionPayload where
  entries : List ImportSelectorEntry
  deriving Repr, BEq, DecidableEq

/-- A source-located import selection. -/
abbrev ImportSelection := Located ImportSelectionPayload

/-- The raw finite names in one hiding clause. -/
structure HidingClausePayload where
  names : List IdentifierOccurrence
  deriving Repr, BEq, DecidableEq

/-- A source-located hiding clause. -/
abbrev HidingClause := Located HidingClausePayload

/-- The one unlocated subordinate import sum. -/
inductive ImportMode where
  | module (alias : Option IdentifierOccurrence)
  | items
      (selection : ImportSelection)
      («hiding» : Option HidingClause)
  deriving Repr, BEq, DecidableEq

/-- The payload of one import declaration. -/
structure ImportDeclPayload where
  moduleRef : ModuleReference
  mode : ImportMode
  deriving Repr, BEq, DecidableEq

/-- A source-located import declaration. -/
abbrev ImportDecl := Located ImportDeclPayload

/-- Constructor selection attached to an exported item. -/
inductive ConstructorSelectionPayload where
  | all (marker : Marker)
  | named (constructors : NonemptyList IdentifierOccurrence)
  deriving Repr, BEq, DecidableEq

/-- A source-located constructor selection. -/
abbrev ConstructorSelection := Located ConstructorSelectionPayload

/-- One named exported item. -/
structure ExportItemPayload where
  name : IdentifierOccurrence
  constructors : Option ConstructorSelection
  deriving Repr, BEq, DecidableEq

/-- A source-located exported item. -/
abbrev ExportItem := Located ExportItemPayload

/-- One local export-list entry. -/
inductive ExportEntryPayload where
  | wildcard (marker : Marker)
  | item (item : ExportItem)
  | allFrom (moduleRef : ModuleReference) (marker : Marker)
  deriving Repr, BEq, DecidableEq

/-- A source-located local export-list entry. -/
abbrev ExportEntry := Located ExportEntryPayload

/-- The raw finite entries of one local export list. -/
structure LocalExportListPayload where
  entries : List ExportEntry
  deriving Repr, BEq, DecidableEq

/-- A source-located local export list. -/
abbrev LocalExportList := Located LocalExportListPayload

/-- One remote export-selection entry. -/
inductive RemoteExportEntryPayload where
  | wildcard (marker : Marker)
  | item (item : ExportItem)
  deriving Repr, BEq, DecidableEq

/-- A source-located remote export-selection entry. -/
abbrev RemoteExportEntry := Located RemoteExportEntryPayload

/-- A source-preserving remote export selection. -/
inductive RemoteExportSelectionPayload where
  | dotWildcard (marker : Marker)
  | braced (entries : List RemoteExportEntry)
  deriving Repr, BEq, DecidableEq

/-- A source-located remote export selection. -/
abbrev RemoteExportSelection := Located RemoteExportSelectionPayload

/-- The complete payload of one export declaration. -/
inductive ExportMode where
  | local (selection : LocalExportList)
  | module
      (moduleRef : ModuleReference)
      (alias : Option IdentifierOccurrence)
  | from
      (moduleRef : ModuleReference)
      (selection : RemoteExportSelection)
  deriving Repr, BEq, DecidableEq

/-- A source-located export declaration. -/
abbrev ExportDecl := Located ExportMode

/-- A literal retaining both source spelling and decoded data. -/
inductive LiteralPayload where
  | decimal (spelling : String) (digits : String)
  | hexadecimal (spelling : String) (digits : String)
  | string (spelling : String) (decoded : String)
  deriving Repr, BEq, DecidableEq

/-- A source-located literal. -/
abbrev Literal := Located LiteralPayload

/-- A source-preserving type expression payload. -/
inductive TypeExprPayload where
  | named
      (name : QualifiedName)
      (arguments : Option (NonemptyList (Located TypeExprPayload)))
  | proxy
      (marker : Located Unit)
      (inner : Located TypeExprPayload)
  | «function»
      (domain : Located TypeExprPayload)
      (codomain : Located TypeExprPayload)
  | tuple (elements : List (Located TypeExprPayload))
  | group (inner : Located TypeExprPayload)
  | comptime (marker : Marker) (inner : Located TypeExprPayload)

/-- A source-located type expression. -/
abbrev TypeExpr := Located TypeExprPayload

/-- One universally quantified type binder. -/
inductive ForallBinderPayload where
  | bare (binder : IdentifierOccurrence)
  | bounded
      (binder : IdentifierOccurrence)
      (className : QualifiedName)
      (arguments : Option (NonemptyList TypeExpr))

/-- A source-located universally quantified type binder. -/
abbrev ForallBinder := Located ForallBinderPayload

/-- The nonempty binders of one universal clause. -/
structure ForallClausePayload where
  binders : NonemptyList ForallBinder

/-- A source-located universal clause. -/
abbrev ForallClause := Located ForallClausePayload

/-- One class predicate in a generic context. -/
structure PredicatePayload where
  main : TypeExpr
  className : QualifiedName
  parameters : Option (NonemptyList TypeExpr)

/-- A source-located generic predicate. -/
abbrev Predicate := Located PredicatePayload

/-- A universal clause with its optional predicate context. -/
structure GenericPrefixPayload where
  forallClause : ForallClause
  context : Option (NonemptyList Predicate)

/-- A source-located generic prefix. -/
abbrev GenericPrefix := Located GenericPrefixPayload

/-- One function or lambda parameter. -/
structure ParameterPayload where
  comptime : Option Marker
  name : IdentifierOccurrence
  «type» : Option TypeExpr

/-- A source-located parameter. -/
abbrev Parameter := Located ParameterPayload

/-- The shared signature of functions and class methods. -/
structure FunctionSignaturePayload where
  genericPrefix : Option GenericPrefix
  «public» : Option Marker
  payable : Option Marker
  name : IdentifierOccurrence
  parameters : List Parameter
  returnType : Option TypeExpr

/-- A source-located function signature. -/
abbrev FunctionSignature := Located FunctionSignaturePayload

/-- The retained delimiter origin of one body. -/
inductive BodyOrigin where
  | braced (openBrace : SourceSpan) (closeBrace : SourceSpan)
  | matchArm (fatArrow : SourceSpan)
  deriving Repr, BEq, DecidableEq

/-- The sole prefix operator. -/
inductive PrefixOperator where
  | logicalNot
  deriving Repr, BEq, DecidableEq

/-- The closed infix-operator set. -/
inductive InfixOperator where
  | multiply
  | divide
  | modulo
  | add
  | subtract
  | bitAnd
  | bitXor
  | bitOr
  | less
  | greater
  | lessEqual
  | greaterEqual
  | equal
  | notEqual
  | logicalAnd
  | logicalOr
  deriving Repr, BEq, DecidableEq

/-- The closed assignment-operator set. -/
inductive AssignmentOperator where
  | equal
  | addEqual
  | subtractEqual
  | bitXorEqual
  | bitAndEqual
  | bitOrEqual
  | moduloEqual
  deriving Repr, BEq, DecidableEq

mutual

/-- A source-preserving expression payload. -/
inductive ExpressionPayload where
  | name (name : IdentifierOccurrence)
  | call
      (callee : Located ExpressionPayload)
      (arguments : List (Located ExpressionPayload))
  | select
      (receiver : Located ExpressionPayload)
      (field : IdentifierOccurrence)
  | dotConstructor
      (marker : Located Unit)
      (name : IdentifierOccurrence)
      (arguments : Option (List (Located ExpressionPayload)))
  | proxy (marker : Located Unit) («type» : TypeExpr)
  | literal (literal : Literal)
  | lambda
      (parameters : List Parameter)
      (returnType : Option TypeExpr)
      (body : Located BodyPayload)
  | annotation
      (expression : Located ExpressionPayload)
      («type» : TypeExpr)
  | keywordConditional
      (condition : Located ExpressionPayload)
      (thenBranch : Located ExpressionPayload)
      (elseBranch : Located ExpressionPayload)
  | ternaryConditional
      (condition : Located ExpressionPayload)
      (thenBranch : Located ExpressionPayload)
      (elseBranch : Located ExpressionPayload)
  | index
      (receiver : Located ExpressionPayload)
      (index : Located ExpressionPayload)
  | prefix
      (operator : Located PrefixOperator)
      (operand : Located ExpressionPayload)
  | infix
      (operator : Located InfixOperator)
      (left : Located ExpressionPayload)
      (right : Located ExpressionPayload)
  | tuple (elements : List (Located ExpressionPayload))
  | group (inner : Located ExpressionPayload)

/-- A source-preserving pattern payload. -/
inductive PatternPayload where
  | named
      (name : QualifiedName)
      (arguments : Option (NonemptyList (Located PatternPayload)))
  | dotConstructor
      (marker : Located Unit)
      (name : IdentifierOccurrence)
      (arguments : Option (NonemptyList (Located PatternPayload)))
  | wildcard (marker : Marker)
  | literal (literal : Literal)
  | comptime (marker : Marker) (expression : Located ExpressionPayload)
  | tuple (elements : List (Located PatternPayload))
  | group (inner : Located PatternPayload)

/-- The source-preserving payload of one statement body. -/
structure BodyPayload where
  origin : BodyOrigin
  statements : List (Located StatementPayload)

/-- One source-preserving let binding. -/
structure LetBindingPayload where
  comptime : Option Marker
  name : IdentifierOccurrence
  «type» : Option TypeExpr
  initializer : Option (Located ExpressionPayload)

/-- One source-preserving initializer in a `for` statement. -/
inductive ForInitItemPayload where
  | letBinding (binding : Located LetBindingPayload)
  | assignment
      (operator : Located AssignmentOperator)
      (left : Located ExpressionPayload)
      (right : Located ExpressionPayload)
  | expression (expression : Located ExpressionPayload)

/-- One source-preserving post item in a `for` statement. -/
inductive ForPostItemPayload where
  | assignment
      (operator : Located AssignmentOperator)
      (left : Located ExpressionPayload)
      (right : Located ExpressionPayload)
  | expression (expression : Located ExpressionPayload)

/-- One source-preserving match arm. -/
structure MatchArmPayload where
  patterns : NonemptyList (Located PatternPayload)
  body : Located BodyPayload

/-- A source-preserving statement payload. -/
inductive StatementPayload where
  | assignment
      (operator : Located AssignmentOperator)
      (left : Located ExpressionPayload)
      (right : Located ExpressionPayload)
  | letBinding (binding : Located LetBindingPayload)
  | block (body : Located BodyPayload)
  | expression
      (expression : Located ExpressionPayload)
      (terminator : Option SourceSpan)
  | «return»
      (value : Option (Located ExpressionPayload))
      (terminator : SourceSpan)
  | «match»
      (scrutinees : NonemptyList (Located ExpressionPayload))
      (arms : NonemptyList (Located MatchArmPayload))
      (terminator : Option SourceSpan)
  | assembly (slice : AssemblySlice)
  | ifThenElse
      (condition : Located ExpressionPayload)
      (thenBody : Located BodyPayload)
      (elseBody : Option (Located BodyPayload))
  | forLoop
      (initializers : List (Located ForInitItemPayload))
      (condition : Located ExpressionPayload)
      (post : List (Located ForPostItemPayload))
      (body : Located BodyPayload)
  | «break» (terminator : SourceSpan)
  | «continue» (terminator : SourceSpan)

end

/-- A source-located expression. -/
abbrev Expression := Located ExpressionPayload

/-- A source-located pattern. -/
abbrev Pattern := Located PatternPayload

/-- A source-located statement body. -/
abbrev Body := Located BodyPayload

/-- A source-located let binding. -/
abbrev LetBinding := Located LetBindingPayload

/-- A source-located initializer in a `for` statement. -/
abbrev ForInitItem := Located ForInitItemPayload

/-- A source-located post item in a `for` statement. -/
abbrev ForPostItem := Located ForPostItemPayload

/-- A source-located match arm. -/
abbrev MatchArm := Located MatchArmPayload

/-- A source-located statement. -/
abbrev Statement := Located StatementPayload

/-- One declaration-only class method. -/
structure ClassMethodDeclPayload where
  signature : FunctionSignature
  terminator : SourceSpan

/-- A source-located declaration-only class method. -/
abbrev ClassMethodDecl := Located ClassMethodDeclPayload

/-- One function declaration payload. -/
structure FunctionDeclPayload where
  signature : FunctionSignature
  body : Body

/-- A source-located function declaration. -/
abbrev FunctionDecl := Located FunctionDeclPayload

/-- One fallback declaration payload. -/
structure FallbackDeclPayload where
  genericPrefix : Option GenericPrefix
  «public» : Option Marker
  payable : Option Marker
  marker : Marker
  parameters : List Parameter
  returnType : Option TypeExpr
  body : Body

/-- A source-located fallback declaration. -/
abbrev FallbackDecl := Located FallbackDeclPayload

/-- One contract-constructor declaration payload. -/
structure ContractConstructorDeclPayload where
  «public» : Option Marker
  payable : Option Marker
  marker : Marker
  parameters : List Parameter
  body : Body

/-- A source-located contract-constructor declaration. -/
abbrev ContractConstructorDecl := Located ContractConstructorDeclPayload

/-- One data constructor payload. -/
structure DataConstructorPayload where
  name : IdentifierOccurrence
  fields : Option (NonemptyList TypeExpr)

/-- A source-located data constructor. -/
abbrev DataConstructor := Located DataConstructorPayload

/-- One algebraic-data declaration payload. -/
structure DataDeclPayload where
  name : IdentifierOccurrence
  parameters : Option (NonemptyList IdentifierOccurrence)
  constructors : Option (NonemptyList DataConstructor)

/-- A source-located algebraic-data declaration. -/
abbrev DataDecl := Located DataDeclPayload

/-- One type-alias declaration payload. -/
structure TypeAliasDeclPayload where
  name : IdentifierOccurrence
  parameters : Option (NonemptyList IdentifierOccurrence)
  body : TypeExpr

/-- A source-located type-alias declaration. -/
abbrev TypeAliasDecl := Located TypeAliasDeclPayload

/-- One type-class declaration payload. -/
structure ClassDeclPayload where
  genericPrefix : Option GenericPrefix
  main : TypeExpr
  className : IdentifierOccurrence
  parameters : Option (NonemptyList TypeExpr)
  methods : List ClassMethodDecl

/-- A source-located type-class declaration. -/
abbrev ClassDecl := Located ClassDeclPayload

/-- One type-class instance declaration payload. -/
structure InstanceDeclPayload where
  genericPrefix : Option GenericPrefix
  «default» : Option Marker
  main : TypeExpr
  className : QualifiedName
  parameters : Option (NonemptyList TypeExpr)
  methods : List FunctionDecl

/-- A source-located type-class instance declaration. -/
abbrev InstanceDecl := Located InstanceDeclPayload

/-- One pragma declaration payload. -/
structure PragmaDeclPayload where
  kind : Located PragmaKind
  targets : List IdentifierOccurrence
  deriving Repr, BEq, DecidableEq

/-- A source-located pragma declaration. -/
abbrev PragmaDecl := Located PragmaDeclPayload

/-- One contract field declaration payload. -/
structure FieldDeclPayload where
  name : IdentifierOccurrence
  «type» : TypeExpr
  initializer : Option Expression

/-- A source-located contract field declaration. -/
abbrev FieldDecl := Located FieldDeclPayload

/-- One source-ordered contract member payload. -/
inductive ContractMemberPayload where
  | dataDecl (declaration : DataDecl)
  | typeAlias (declaration : TypeAliasDecl)
  | field (declaration : FieldDecl)
  | «function» (declaration : FunctionDecl)
  | fallback (declaration : FallbackDecl)
  | «constructor» (declaration : ContractConstructorDecl)

/-- A source-located contract member. -/
abbrev ContractMember := Located ContractMemberPayload

/-- One contract declaration payload. -/
structure ContractDeclPayload where
  name : IdentifierOccurrence
  parameters : Option (NonemptyList IdentifierOccurrence)
  members : List ContractMember

/-- A source-located contract declaration. -/
abbrev ContractDecl := Located ContractDeclPayload

/-- One source-ordered top-level item payload. -/
inductive TopItemPayload where
  | importDecl (declaration : ImportDecl)
  | exportDecl (declaration : ExportDecl)
  | pragmaDecl (declaration : PragmaDecl)
  | dataDecl (declaration : DataDecl)
  | typeAliasDecl (declaration : TypeAliasDecl)
  | classDecl (declaration : ClassDecl)
  | instanceDecl (declaration : InstanceDecl)
  | contractDecl (declaration : ContractDecl)
  | functionDecl (declaration : FunctionDecl)

/-- A source-located top-level item. -/
abbrev TopItem := Located TopItemPayload

/-- The complete source-preserving payload of one parsed module. -/
structure ParsedModuleV1Payload where
  source : SourceId
  items : List TopItem

/-- A complete source-located parsed module. -/
abbrev ParsedModuleV1 := Located ParsedModuleV1Payload

end Solcore.Surface.Multi
