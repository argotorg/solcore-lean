import Solcore.Surface.Multi.ExactTokenExpression

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar

/-!
This module covers the declaration surface of the
m2c-v1 grammar and calls the concrete recursive exact-token visitors directly.
Every declaration body enters `bodyTokenPlan?` in braced mode, so the recursive
visitor also enforces that only the final statement may omit a semicolon.

The covered grammar slice contains 32 grammar rules and 70 `RuleReduction`
constructors when the already-public five-constructor `moduleRef` visitor and
the two generated `optionalComma` constructors are counted.  The only
AST-erased token choice in this slice is the comma before a tail `forall`
binder.  It is therefore the only place this visitor emits an optional slot.
-/

/-- The declaration-layer source rules dispatched by this visitor.  Reusable
`type`/`typeAtom`/`qualifiedName` and recursive syntax visitors are dependencies,
not members of this slice. -/
def declarationTokenPlanCoveredRules : List GrammarRuleId := [
  .module, .topItem, .moduleRef,
  .importDecl, .importEntry, .hidingClause,
  .exportDecl, .localExportEntry, .remoteExportEntry, .exportItem,
  .constructorSelection, .pragmaDecl,
  .genericPrefix, .forallClause, .forallBinder, .optionalComma,
  .predicateList, .predicate,
  .functionSignature, .functionDecl, .classMethod,
  .dataDecl, .dataConstructor, .typeAliasDecl,
  .classDecl, .instanceDecl, .instanceMethod,
  .contractDecl, .contractMember, .fieldDecl, .fallbackDecl,
  .contractConstructorDecl]

/-- Number of source grammar rules represented by the declaration visitor. -/
def declarationTokenPlanGrammarRuleCount : Nat :=
  declarationTokenPlanCoveredRules.length

theorem declarationTokenPlanGrammarRuleCount_eq :
    declarationTokenPlanGrammarRuleCount = 32 := by
  rfl

/-- Number of source `RuleReduction` constructors represented by those rules.
The recursive callback implementations are not included in this count. -/
def declarationTokenPlanReductionConstructorCount : Nat := 70

/-- Exhaustive classes of deliberate `none` results at this layer. -/
inductive DeclarationTokenPlanRejectCase where
  | markerRoleMismatch
  | moduleReferenceShapeMismatch
  | typeGrammarShapeMismatch
  | nonBracedDeclarationBody
  | recursiveSyntaxShapeMismatch
  deriving Repr, BEq, DecidableEq

def declarationTokenPlanRejectCases :
    List DeclarationTokenPlanRejectCase := [
  .markerRoleMismatch,
  .moduleReferenceShapeMismatch,
  .typeGrammarShapeMismatch,
  .nonBracedDeclarationBody,
  .recursiveSyntaxShapeMismatch]

private def plans? {α : Type} (visit : α → Option TokenPlan) :
    List α → Option (List TokenPlan)
  | [] => some []
  | value :: rest => do
      let plan ← visit value
      let restPlans ← plans? visit rest
      pure (plan :: restPlans)

@[simp] private theorem plans?_eq_mapM
    {α : Type} (visit : α → Option TokenPlan) (values : List α) :
    plans? visit values = values.mapM visit := by
  induction values with
  | nil => rfl
  | cons value rest induction =>
      simp only [plans?, List.mapM_cons, induction]

private def nonemptyPlans? {α : Type} (visit : α → Option TokenPlan)
    (values : NonemptyList α) : Option (List TokenPlan) := do
  let headPlan ← visit values.head
  let tailPlans ← plans? visit values.tail
  pure (headPlan :: tailPlans)

private def optionalPlan? {α : Type} (visit : α → Option TokenPlan) :
    Option α → Option TokenPlan
  | none => some .empty
  | some value => visit value

private def markerPlan? (role : SyntaxMarker) (kind : TokenKind)
    (marker : Marker) : Option TokenPlan :=
  if marker.payload = role then
    some (.exact kind marker.span)
  else
    none

private def optionalMarkerPlan? (role : SyntaxMarker) (kind : TokenKind) :
    Option Marker → Option TokenPlan
  | none => some .empty
  | some marker => markerPlan? role kind marker

private def identifierPlans (values : List IdentifierOccurrence) :
    List TokenPlan :=
  values.map identifierPlan

private def nonemptyIdentifierPlans
    (values : NonemptyList IdentifierOccurrence) : List TokenPlan :=
  identifierPlan values.head :: identifierPlans values.tail

private def nonemptyTypePlans?
    (values : NonemptyList TypeExpr) : Option TokenPlan := do
  let plans ← nonemptyTypeExprPlans? values
  pure (.parens (.commaSeparated plans))

private def optionalNonemptyTypePlans? :
    Option (NonemptyList TypeExpr) → Option TokenPlan
  | none => some .empty
  | some values => nonemptyTypePlans? values

private def optionalNonemptyIdentifierPlan :
    Option (NonemptyList IdentifierOccurrence) → TokenPlan
  | none => .empty
  | some values => .parens (.commaSeparated (nonemptyIdentifierPlans values))

private def pipeSeparated : List TokenPlan → TokenPlan
  | [] => .empty
  | first :: rest =>
      .append first <| .concat <| rest.map fun plan =>
        .append (.plain (.symbol .pipe)) plan

private def optionalAliasPlan : Option IdentifierOccurrence → TokenPlan
  | none => .empty
  | some alias => .concat [
      .plain (.hardKeyword .asKw),
      identifierPlan alias]

private def optionalReturnTypePlan? : Option TypeExpr → Option TokenPlan
  | none => some .empty
  | some returnType => do
      let typePlan ← typeExprPlan? returnType
      pure (.append (.plain (.symbol .arrow)) typePlan)

/-! ## Imports -/

def importSelectorEntryPlan?
    (entry : ImportSelectorEntry) : Option TokenPlan := do
  let inner ← match entry.payload with
    | .wildcard marker =>
        markerPlan? .wildcard (.symbol .star) marker
    | .named source alias =>
        some (.append (identifierPlan source) (optionalAliasPlan alias))
  pure (.enclose entry.span inner)

def importSelectionPlan?
    (selection : ImportSelection) : Option TokenPlan := do
  let entries ← plans? importSelectorEntryPlan? selection.payload.entries
  pure (.enclose selection.span <| .concat [
    .plain (.symbol .leftBrace),
    .commaSeparated entries,
    .plain (.symbol .rightBrace)])

def hidingClausePlan? (clause : HidingClause) : Option TokenPlan :=
  some (.enclose clause.span <| .concat [
    .plain (.hardKeyword .hidingKw),
    .plain (.symbol .leftBrace),
    .commaSeparated (identifierPlans clause.payload.names),
    .plain (.symbol .rightBrace)])

def importDeclPlan? (declaration : ImportDecl) : Option TokenPlan := do
  let reference ← moduleReferencePlan? declaration.payload.moduleRef
  let mode ← match declaration.payload.mode with
    | .module alias =>
        some (optionalAliasPlan alias)
    | .items selection hidden => do
        let selectionPlan ← importSelectionPlan? selection
        let hidingPlan ← optionalPlan? hidingClausePlan? hidden
        pure (.concat [
          .plain (.symbol .dot),
          selectionPlan,
          hidingPlan])
  pure (.enclose declaration.span <| .concat [
    .plain (.hardKeyword .importKw),
    reference,
    mode,
    .plain (.symbol .semicolon)])

/-! ## Exports -/

def constructorSelectionPlan?
    (selection : ConstructorSelection) : Option TokenPlan := do
  let inner ← match selection.payload with
    | .all marker => do
        let star ← markerPlan? .wildcard (.symbol .star) marker
        pure (.parens star)
    | .named constructors =>
        pure (.parens (.commaSeparated (nonemptyIdentifierPlans constructors)))
  pure (.enclose selection.span inner)

def exportItemPlan? (item : ExportItem) : Option TokenPlan := do
  let constructors ← optionalPlan? constructorSelectionPlan?
    item.payload.constructors
  pure (.enclose item.span <| .append
    (identifierPlan item.payload.name) constructors)

def localExportEntryPlan? (entry : ExportEntry) : Option TokenPlan := do
  let inner ← match entry.payload with
    | .wildcard marker =>
        markerPlan? .wildcard (.symbol .star) marker
    | .item item =>
        exportItemPlan? item
    | .allFrom moduleRef marker => do
        let reference ← moduleReferencePlan? moduleRef
        let star ← markerPlan? .wildcard (.symbol .star) marker
        pure (.concat [reference, .plain (.symbol .dot), star])
  pure (.enclose entry.span inner)

def localExportListPlan?
    (selection : LocalExportList) : Option TokenPlan := do
  let entries ← plans? localExportEntryPlan? selection.payload.entries
  pure (.enclose selection.span <| .concat [
    .plain (.symbol .leftBrace),
    .commaSeparated entries,
    .plain (.symbol .rightBrace)])

def remoteExportEntryPlan?
    (entry : RemoteExportEntry) : Option TokenPlan := do
  let inner ← match entry.payload with
    | .wildcard marker =>
        markerPlan? .wildcard (.symbol .star) marker
    | .item item =>
        exportItemPlan? item
  pure (.enclose entry.span inner)

def remoteExportSelectionPlan?
    (selection : RemoteExportSelection) : Option TokenPlan := do
  let inner ← match selection.payload with
    | .dotWildcard marker => do
        let star ← markerPlan? .wildcard (.symbol .star) marker
        pure (.append (.plain (.symbol .dot)) star)
    | .braced entries => do
        let entryPlans ← plans? remoteExportEntryPlan? entries
        pure (.concat [
          .plain (.symbol .leftBrace),
          .commaSeparated entryPlans,
          .plain (.symbol .rightBrace)])
  pure (.enclose selection.span inner)

private def remoteSelectionAfterReferencePlan?
    (selection : RemoteExportSelection) : Option TokenPlan :=
  match selection.payload with
  | .dotWildcard _ => remoteExportSelectionPlan? selection
  | .braced _ => do
      let plan ← remoteExportSelectionPlan? selection
      pure (.append (.plain (.symbol .dot)) plan)

def exportDeclPlan? (declaration : ExportDecl) : Option TokenPlan := do
  let mode ← match declaration.payload with
    | .local selection =>
        localExportListPlan? selection
    | .module moduleRef alias => do
        let reference ← moduleReferencePlan? moduleRef
        pure (.append reference (optionalAliasPlan alias))
    | .from moduleRef selection => do
        let reference ← moduleReferencePlan? moduleRef
        let selectionPlan ← remoteSelectionAfterReferencePlan? selection
        pure (.append reference selectionPlan)
  pure (.enclose declaration.span <| .concat [
    .plain (.hardKeyword .exportKw),
    mode,
    .plain (.symbol .semicolon)])

/-! ## Pragmas and generic prefixes -/

def pragmaDeclPlan? (declaration : PragmaDecl) : Option TokenPlan :=
  let targets := match declaration.payload.targets with
    | [] => TokenPlan.empty
    | values@(_ :: _) => .commaSeparated (identifierPlans values)
  some (.enclose declaration.span <| .concat [
    .plain (.hardKeyword .pragmaKw),
    .exact (.pragmaName declaration.payload.kind.payload)
      declaration.payload.kind.span,
    targets,
    .plain (.symbol .semicolon)])

def forallBinderPlan? (binder : ForallBinder) : Option TokenPlan := do
  let inner ← match binder.payload with
    | .bare name =>
        some (identifierPlan name)
    | .bounded name className arguments => do
        let argumentsPlan ← optionalNonemptyTypePlans? arguments
        pure (.concat [
          identifierPlan name,
          .plain (.symbol .colon),
          qualifiedNamePlan className,
          argumentsPlan])
  pure (.enclose binder.span inner)

def forallClausePlan? (clause : ForallClause) : Option TokenPlan := do
  let first ← forallBinderPlan? clause.payload.binders.head
  let rest ← plans? forallBinderPlan? clause.payload.binders.tail
  pure (forallClausePlanWith first rest clause)

def predicatePlan? (predicate : Predicate) : Option TokenPlan := do
  let main ← typeAtomPlan? predicate.payload.main
  let parameters ← optionalNonemptyTypePlans? predicate.payload.parameters
  pure (.enclose predicate.span <| .concat [
    main,
    .plain (.symbol .colon),
    qualifiedNamePlan predicate.payload.className,
    parameters])

def predicateListPlan?
    (predicates : NonemptyList Predicate) : Option TokenPlan := do
  let plans ← nonemptyPlans? predicatePlan? predicates
  pure (.commaSeparated plans)

def genericPrefixPlan? (generic : GenericPrefix) : Option TokenPlan := do
  let forallPlan ← forallClausePlan? generic.payload.forallClause
  let contextPlan ← match generic.payload.context with
    | none => some TokenPlan.empty
    | some predicates => do
        let predicatesPlan ← predicateListPlan? predicates
        pure (.append predicatesPlan (.plain (.symbol .fatArrow)))
  pure (.enclose generic.span (.append forallPlan contextPlan))

/-! ## Signatures, functions, and nominal declarations -/

def functionSignaturePlan?
    (signature : FunctionSignature) : Option TokenPlan := do
  let generic ← optionalPlan? genericPrefixPlan?
    signature.payload.genericPrefix
  let publicModifier ← optionalMarkerPlan? .publicModifier
    (.hardKeyword .publicKw) signature.payload.public
  let payableModifier ← optionalMarkerPlan? .payableModifier
    (.hardKeyword .payableKw) signature.payload.payable
  let parameters ← plans? parameterTokenPlan? signature.payload.parameters
  let returnType ← optionalReturnTypePlan? signature.payload.returnType
  pure (.enclose signature.span <| .concat [
    generic,
    publicModifier,
    payableModifier,
    .plain (.hardKeyword .functionKw),
    identifierPlan signature.payload.name,
    .parens (.commaSeparated parameters),
    returnType])

def functionDeclPlan?
    (declaration : FunctionDecl) : Option TokenPlan := do
  let signature ← functionSignaturePlan? declaration.payload.signature
  let body ← bodyTokenPlan? .braced declaration.payload.body
  pure (.enclose declaration.span (.append signature body))

def classMethodDeclPlan?
    (declaration : ClassMethodDecl) : Option TokenPlan := do
  let signature ← functionSignaturePlan? declaration.payload.signature
  pure (.enclose declaration.span <| .append signature <|
    .exact (.symbol .semicolon) declaration.payload.terminator)

def dataConstructorPlan?
    (constructor : DataConstructor) : Option TokenPlan := do
  let fields ← optionalNonemptyTypePlans? constructor.payload.fields
  pure (.enclose constructor.span <| .append
    (identifierPlan constructor.payload.name) fields)

def dataDeclPlan? (declaration : DataDecl) : Option TokenPlan := do
  let constructorPlan ← match declaration.payload.constructors with
    | none => some TokenPlan.empty
    | some constructors => do
        let plans ← nonemptyPlans? dataConstructorPlan? constructors
        pure (.append (.plain (.symbol .equal)) (pipeSeparated plans))
  pure (.enclose declaration.span <| .concat [
    .plain (.hardKeyword .dataKw),
    identifierPlan declaration.payload.name,
    optionalNonemptyIdentifierPlan declaration.payload.parameters,
    constructorPlan,
    .plain (.symbol .semicolon)])

def typeAliasDeclPlan? (declaration : TypeAliasDecl) : Option TokenPlan := do
  let body ← typeExprPlan? declaration.payload.body
  pure (.enclose declaration.span <| .concat [
    .plain (.hardKeyword .typeKw),
    identifierPlan declaration.payload.name,
    optionalNonemptyIdentifierPlan declaration.payload.parameters,
    .plain (.symbol .equal),
    body,
    .plain (.symbol .semicolon)])

def classDeclPlan?
    (declaration : ClassDecl) : Option TokenPlan := do
  let generic ← optionalPlan? genericPrefixPlan?
    declaration.payload.genericPrefix
  let main ← typeAtomPlan? declaration.payload.main
  let parameters ← optionalNonemptyTypePlans? declaration.payload.parameters
  let methods ← plans? classMethodDeclPlan?
    declaration.payload.methods
  pure (.enclose declaration.span <| .concat [
    generic,
    .plain (.hardKeyword .classKw),
    main,
    .plain (.symbol .colon),
    identifierPlan declaration.payload.className,
    parameters,
    .plain (.symbol .leftBrace),
    .concat methods,
    .plain (.symbol .rightBrace)])

def instanceDeclPlan?
    (declaration : InstanceDecl) : Option TokenPlan := do
  let generic ← optionalPlan? genericPrefixPlan?
    declaration.payload.genericPrefix
  let defaultModifier ← optionalMarkerPlan? .defaultModifier
    (.hardKeyword .defaultKw) declaration.payload.default
  let main ← typeAtomPlan? declaration.payload.main
  let parameters ← optionalNonemptyTypePlans? declaration.payload.parameters
  let methods ← plans? functionDeclPlan? declaration.payload.methods
  pure (.enclose declaration.span <| .concat [
    generic,
    defaultModifier,
    .plain (.hardKeyword .instanceKw),
    main,
    .plain (.symbol .colon),
    qualifiedNamePlan declaration.payload.className,
    parameters,
    .plain (.symbol .leftBrace),
    .concat methods,
    .plain (.symbol .rightBrace)])

/-! ## Contracts -/

def fieldDeclPlan?
    (declaration : FieldDecl) : Option TokenPlan := do
  let typePlan ← typeExprPlan? declaration.payload.type
  let initializer ← match declaration.payload.initializer with
    | none => some TokenPlan.empty
    | some expression => do
        let expressionPlan ← expressionTokenPlan? expression
        pure (.append (.plain (.symbol .equal)) expressionPlan)
  pure (.enclose declaration.span <| .concat [
    identifierPlan declaration.payload.name,
    .plain (.symbol .colon),
    typePlan,
    initializer,
    .plain (.symbol .semicolon)])

def fallbackDeclPlan?
    (declaration : FallbackDecl) : Option TokenPlan := do
  let generic ← optionalPlan? genericPrefixPlan?
    declaration.payload.genericPrefix
  let publicModifier ← optionalMarkerPlan? .publicModifier
    (.hardKeyword .publicKw) declaration.payload.public
  let payableModifier ← optionalMarkerPlan? .payableModifier
    (.hardKeyword .payableKw) declaration.payload.payable
  let fallbackMarker ← markerPlan? .fallbackName
    (.hardKeyword .fallbackKw) declaration.payload.marker
  let parameters ← plans? parameterTokenPlan? declaration.payload.parameters
  let returnType ← optionalReturnTypePlan? declaration.payload.returnType
  let body ← bodyTokenPlan? .braced declaration.payload.body
  pure (.enclose declaration.span <| .concat [
    generic,
    publicModifier,
    payableModifier,
    fallbackMarker,
    .parens (.commaSeparated parameters),
    returnType,
    body])

def contractConstructorDeclPlan?
    (declaration : ContractConstructorDecl) : Option TokenPlan := do
  let publicModifier ← optionalMarkerPlan? .publicModifier
    (.hardKeyword .publicKw) declaration.payload.public
  let payableModifier ← optionalMarkerPlan? .payableModifier
    (.hardKeyword .payableKw) declaration.payload.payable
  let constructorMarker ← markerPlan? .contractConstructorName
    (.hardKeyword .constructorKw) declaration.payload.marker
  let parameters ← plans? parameterTokenPlan? declaration.payload.parameters
  let body ← bodyTokenPlan? .braced declaration.payload.body
  pure (.enclose declaration.span <| .concat [
    publicModifier,
    payableModifier,
    constructorMarker,
    .parens (.commaSeparated parameters),
    body])

def contractMemberPlan?
    (member : ContractMember) : Option TokenPlan := do
  let inner ← match member.payload with
    | .dataDecl declaration =>
        dataDeclPlan? declaration
    | .typeAlias declaration =>
        typeAliasDeclPlan? declaration
    | .field declaration =>
        fieldDeclPlan? declaration
    | .function declaration =>
        functionDeclPlan? declaration
    | .fallback declaration =>
        fallbackDeclPlan? declaration
    | .constructor declaration =>
        contractConstructorDeclPlan? declaration
  pure (.enclose member.span inner)

def contractDeclPlan?
    (declaration : ContractDecl) : Option TokenPlan := do
  let members ← plans? contractMemberPlan?
    declaration.payload.members
  pure (.enclose declaration.span <| .concat [
    .plain (.hardKeyword .contractKw),
    identifierPlan declaration.payload.name,
    optionalNonemptyIdentifierPlan declaration.payload.parameters,
    .plain (.symbol .leftBrace),
    .concat members,
    .plain (.symbol .rightBrace)])

/-! ## Top-level and module visitors -/

def topItemPlan?
    (item : TopItem) : Option TokenPlan := do
  let inner ← match item.payload with
    | .importDecl declaration => importDeclPlan? declaration
    | .exportDecl declaration => exportDeclPlan? declaration
    | .pragmaDecl declaration => pragmaDeclPlan? declaration
    | .dataDecl declaration => dataDeclPlan? declaration
    | .typeAliasDecl declaration => typeAliasDeclPlan? declaration
    | .classDecl declaration => classDeclPlan? declaration
    | .instanceDecl declaration => instanceDeclPlan? declaration
    | .contractDecl declaration => contractDeclPlan? declaration
    | .functionDecl declaration => functionDeclPlan? declaration
  pure (.enclose item.span inner)

/-- Build the exact retained-token plan for every declaration in a module.
The module itself is not enclosed: its span is the whole file and may include
leading/trailing trivia, while token plans intentionally describe retained
tokens only. -/
def declarationModulePlan?
    (module : ParsedModuleV1) : Option TokenPlan := do
  let items ← plans? topItemPlan? module.payload.items
  pure (.concat items)

/-- An empty module contributes no retained-token slots. -/
@[simp] theorem declarationModulePlan?_nil
    (span : SourceSpan) (source : Solcore.Workspace.SourceId) :
    declarationModulePlan? ⟨span, ⟨source, []⟩⟩ = some .empty := by
  rfl

/-- Module planning composes the first top-level item with the recursively
planned suffix in source order. -/
@[simp] theorem declarationModulePlan?_cons
    (span : SourceSpan) (source : Solcore.Workspace.SourceId)
    (item : TopItem) (rest : List TopItem) :
    declarationModulePlan? ⟨span, ⟨source, item :: rest⟩⟩ = (do
      let head ← topItemPlan? item
      let tail ← declarationModulePlan? ⟨span, ⟨source, rest⟩⟩
      pure (head.append tail)) := by
  unfold declarationModulePlan?
  simp only [plans?]
  cases headEq : topItemPlan? item with
  | none => simp
  | some head =>
      cases tailEq : plans? topItemPlan? rest with
      | none => simp
      | some tail =>
          simp [TokenPlan.concat, TokenPlan.append]

/-- Module planning is the ordinary pointwise visitor followed by plan
concatenation. -/
theorem declarationModulePlan?_eq_mapM (module : ParsedModuleV1) :
    declarationModulePlan? module =
      Option.map TokenPlan.concat
        (module.payload.items.mapM topItemPlan?) := by
  unfold declarationModulePlan?
  rw [plans?_eq_mapM]
  cases result : module.payload.items.mapM topItemPlan? <;> simp

/-!
Rejected AST shapes are explicit `none` results:

* wrong marker roles for wildcard/public/payable/default/fallback/constructor;
* invalid module-reference classification (`moduleReferencePlan?`);
* a non-atomic predicate/class/instance head, a singleton tuple, or another
  grammar-impossible type shape (`typeAtomPlan?` / `typeExprPlan?`);
* a match-arm-origin body in any declaration position;
* any parameter, expression, statement, or terminal-statement placement rejected
  by the concrete recursive visitor.

Nonempty grammar sites are represented by `NonemptyList`, so empty bounded
arguments, predicate lists, data parameters/fields/constructors, class
arguments, and contract parameters cannot be manufactured through these AST
fields.  Every ordinary list site is rebuilt with its grammar separator; only
the erased tail-binder comma uses `TokenPlan.optional`.
-/

end Solcore.Surface.Multi
