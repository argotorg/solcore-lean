import Solcore.Surface.Multi.ActionIntervalLocation
import Solcore.Surface.Multi.RuleIntervalLocationWrappedCases
import Solcore.Surface.Multi.RuleIntervalLocationWrappedDeclarationCases
import Solcore.Surface.Multi.RuleIntervalLocationWrappedExpressionCases

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar
open Solcore.Workspace

namespace RuleReduction

open RuleReduction.WrappedLocation

/-- The source reductions whose semantic locations depend on named internal
endpoints rather than only on the complete consumed interval. -/
inductive EndpointSensitiveRuleKind where
  | importDeclItems
  | exportDeclLocal
  | exportDeclWildcard
  | exportDeclBraced
  | matchArm
  | logicalOr
  | logicalAnd
  | bitOr
  | bitXor
  | bitAnd
  | additive
  | multiplicative
  | postfix
  deriving DecidableEq, Repr

namespace EndpointSensitiveRuleKind

/-- Exhaustive registry in source-rule declaration order. -/
def all : List EndpointSensitiveRuleKind := [
  .importDeclItems,
  .exportDeclLocal,
  .exportDeclWildcard,
  .exportDeclBraced,
  .matchArm,
  .logicalOr,
  .logicalAnd,
  .bitOr,
  .bitXor,
  .bitAnd,
  .additive,
  .multiplicative,
  .postfix
]

@[simp] theorem all_length : all.length = 13 := by
  rfl

theorem mem_all (kind : EndpointSensitiveRuleKind) : kind ∈ all := by
  cases kind <;> simp [all]

theorem all_nodup : all.Nodup := by
  simp [all]

end EndpointSensitiveRuleKind

/-- Proof that a reduction is one of the thirteen endpoint-sensitive source
constructors, retaining its precise constructor kind. -/
inductive EndpointSensitiveRuleCase
    {file : WorkspaceFile} {tokens : List Token} :
    {rule : GrammarRuleId} → {origin finish : Boundary tokens} →
      {input : EbnfValue file tokens (m2cV1.rhs rule)} →
      {output : RuleValue rule} →
      RuleReduction file tokens rule origin finish input output → Prop where
  | importDeclItems
      (origin finish : Boundary tokens)
      (importKw : MatchedTerminal file tokens (.hardKeyword .importKw))
      (reference : ModuleReference)
      (dot : MatchedTerminal file tokens (.symbol .dot))
      (openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
      (entries : List ImportSelectorEntry)
      (closeBrace : MatchedTerminal file tokens (.symbol .rightBrace))
      (hidingValue : Option HidingClause)
      (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
      (witness : ConsumedSpanWitness file tokens origin finish) :
      EndpointSensitiveRuleCase
        (RuleReduction.importDeclItems origin finish importKw reference dot
          openBrace entries closeBrace hidingValue semicolon witness)
  | exportDeclLocal
      (origin finish : Boundary tokens)
      (exportKw : MatchedTerminal file tokens (.hardKeyword .exportKw))
      (openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
      (entries : List ExportEntry)
      (closeBrace : MatchedTerminal file tokens (.symbol .rightBrace))
      (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
      (witness : ConsumedSpanWitness file tokens origin finish) :
      EndpointSensitiveRuleCase
        (RuleReduction.exportDeclLocal origin finish exportKw openBrace entries
          closeBrace semicolon witness)
  | exportDeclWildcard
      (origin finish : Boundary tokens)
      (exportKw : MatchedTerminal file tokens (.hardKeyword .exportKw))
      (reference : ModuleReference)
      (dot : MatchedTerminal file tokens (.symbol .dot))
      (star : MatchedTerminal file tokens (.symbol .star))
      (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
      (starMarker : RuleReduction.MarkerProjects file tokens star .wildcard)
      (witness : ConsumedSpanWitness file tokens origin finish) :
      EndpointSensitiveRuleCase
        (RuleReduction.exportDeclWildcard origin finish exportKw reference dot
          star semicolon starMarker witness)
  | exportDeclBraced
      (origin finish : Boundary tokens)
      (exportKw : MatchedTerminal file tokens (.hardKeyword .exportKw))
      (reference : ModuleReference)
      (dot : MatchedTerminal file tokens (.symbol .dot))
      (openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
      (entries : List RemoteExportEntry)
      (closeBrace : MatchedTerminal file tokens (.symbol .rightBrace))
      (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
      (witness : ConsumedSpanWitness file tokens origin finish) :
      EndpointSensitiveRuleCase
        (RuleReduction.exportDeclBraced origin finish exportKw reference dot
          openBrace entries closeBrace semicolon witness)
  | matchArm
      {origin finish : Boundary tokens}
      {input : EbnfValue file tokens (m2cV1.rhs .matchArm)}
      {output : RuleValue .matchArm}
      (reduces : RuleReduction file tokens .matchArm
        origin finish input output) :
      EndpointSensitiveRuleCase reduces
  | logicalOr
      {origin finish : Boundary tokens}
      {input : EbnfValue file tokens (m2cV1.rhs .logicalOr)}
      {output : RuleValue .logicalOr}
      (reduces : RuleReduction file tokens .logicalOr
        origin finish input output) :
      EndpointSensitiveRuleCase reduces
  | logicalAnd
      {origin finish : Boundary tokens}
      {input : EbnfValue file tokens (m2cV1.rhs .logicalAnd)}
      {output : RuleValue .logicalAnd}
      (reduces : RuleReduction file tokens .logicalAnd
        origin finish input output) :
      EndpointSensitiveRuleCase reduces
  | bitOr
      {origin finish : Boundary tokens}
      {input : EbnfValue file tokens (m2cV1.rhs .bitOr)}
      {output : RuleValue .bitOr}
      (reduces : RuleReduction file tokens .bitOr
        origin finish input output) :
      EndpointSensitiveRuleCase reduces
  | bitXor
      {origin finish : Boundary tokens}
      {input : EbnfValue file tokens (m2cV1.rhs .bitXor)}
      {output : RuleValue .bitXor}
      (reduces : RuleReduction file tokens .bitXor
        origin finish input output) :
      EndpointSensitiveRuleCase reduces
  | bitAnd
      {origin finish : Boundary tokens}
      {input : EbnfValue file tokens (m2cV1.rhs .bitAnd)}
      {output : RuleValue .bitAnd}
      (reduces : RuleReduction file tokens .bitAnd
        origin finish input output) :
      EndpointSensitiveRuleCase reduces
  | additive
      {origin finish : Boundary tokens}
      {input : EbnfValue file tokens (m2cV1.rhs .additive)}
      {output : RuleValue .additive}
      (reduces : RuleReduction file tokens .additive
        origin finish input output) :
      EndpointSensitiveRuleCase reduces
  | multiplicative
      {origin finish : Boundary tokens}
      {input : EbnfValue file tokens (m2cV1.rhs .multiplicative)}
      {output : RuleValue .multiplicative}
      (reduces : RuleReduction file tokens .multiplicative
        origin finish input output) :
      EndpointSensitiveRuleCase reduces
  | postfix
      {origin finish : Boundary tokens}
      {input : EbnfValue file tokens (m2cV1.rhs .postfix)}
      {output : RuleValue .postfix}
      (reduces : RuleReduction file tokens .postfix
        origin finish input output) :
      EndpointSensitiveRuleCase reduces

/-- Complete, proof-relevant source-location partition for all source-rule
reductions. -/
inductive SourceRuleLocationCase
    {file : WorkspaceFile} {tokens : List Token} :
    {rule : GrammarRuleId} → {origin finish : Boundary tokens} →
      {input : EbnfValue file tokens (m2cV1.rhs rule)} →
      {output : RuleValue rule} →
      RuleReduction file tokens rule origin finish input output → Prop where
  | module
      {origin finish : Boundary tokens}
      {input : EbnfValue file tokens (m2cV1.rhs .module)}
      {output : RuleValue .module}
      (reduces : RuleReduction file tokens .module
        origin finish input output) :
      SourceRuleLocationCase reduces
  | contextFree
      {rule : GrammarRuleId} {origin finish : Boundary tokens}
      {input : EbnfValue file tokens (m2cV1.rhs rule)}
      {output : RuleValue rule}
      {reduces : RuleReduction file tokens rule origin finish input output}
      (classified : ContextFreeLocationCase reduces) :
      SourceRuleLocationCase reduces
  | endpoint
      {rule : GrammarRuleId} {origin finish : Boundary tokens}
      {input : EbnfValue file tokens (m2cV1.rhs rule)}
      {output : RuleValue rule}
      {reduces : RuleReduction file tokens rule origin finish input output}
      (classified : EndpointSensitiveRuleCase reduces) :
      SourceRuleLocationCase reduces

/-- The numeric partition agrees with the complete 174-constructor source
reduction relation. -/
@[simp] theorem source_rule_location_case_count :
    1 + (38 +
      (ExactWrappedLocationCase.all.length +
        ProjectedWrappedLocationCase.all.length) + 1) +
      EndpointSensitiveRuleKind.all.length = 174 := by
  rfl

/-- Every source reduction belongs to an implemented location-proof strategy
family.  Constructor elimination makes additions to `RuleReduction`
visible here as a new proof obligation. -/
theorem sourceRuleLocationCase
    {file : WorkspaceFile} {tokens : List Token}
    {rule : GrammarRuleId} {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs rule)}
    {output : RuleValue rule}
    (reduces : RuleReduction file tokens rule origin finish input output) :
    SourceRuleLocationCase reduces := by
  cases reduces with
  | module => exact .module _
  | topItemImport =>
      exact .contextFree (.wrapped (by apply topItemImport_case))
  | topItemExport =>
      exact .contextFree (.wrapped (by apply topItemExport_case))
  | topItemPragma =>
      exact .contextFree (.wrapped (by apply topItemPragma_case))
  | topItemData =>
      exact .contextFree (.wrapped (by apply topItemData_case))
  | topItemTypeAlias =>
      exact .contextFree (.wrapped (by apply topItemTypeAlias_case))
  | topItemClass =>
      exact .contextFree (.wrapped (by apply topItemClass_case))
  | topItemInstance =>
      exact .contextFree (.wrapped (by apply topItemInstance_case))
  | topItemContract =>
      exact .contextFree (.wrapped (by apply topItemContract_case))
  | topItemFunction =>
      exact .contextFree (.wrapped (by apply topItemFunction_case))
  | moduleRefExternal =>
      exact .contextFree (.wrapped (by
        apply moduleRefExternal_case <;> assumption))
  | moduleRefStandard =>
      exact .contextFree (.wrapped (by
        apply moduleRefStandard_case <;> assumption))
  | moduleRefLibraryRoot =>
      exact .contextFree (.wrapped (by
        apply moduleRefLibraryRoot_case <;> assumption))
  | moduleRefRelativeLibraryEmpty =>
      exact .contextFree (.wrapped (by
        apply moduleRefRelativeLibraryEmpty_case <;> assumption))
  | moduleRefRelativeOther =>
      exact .contextFree (.wrapped (by
        apply moduleRefRelativeOther_case <;> assumption))
  | importDeclModule =>
      exact .contextFree (.wrapped (by apply importDeclModule_case))
  | importDeclAliased =>
      exact .contextFree (.wrapped (by
        apply importDeclAliased_case <;> assumption))
  | importDeclItems =>
      exact .endpoint (by apply EndpointSensitiveRuleCase.importDeclItems)
  | importEntryWildcard =>
      exact .contextFree (.wrapped (by apply importEntryWildcard_case))
  | importEntryNamed =>
      exact .contextFree (.wrapped (by
        apply importEntryNamed_case <;> assumption))
  | importEntryAliased =>
      exact .contextFree (.wrapped (by
        apply importEntryAliased_case <;> assumption))
  | hidingClause =>
      exact .contextFree (.wrapped (by
        apply hidingClause_case <;> assumption))
  | exportDeclLocal =>
      exact .endpoint (by apply EndpointSensitiveRuleCase.exportDeclLocal)
  | exportDeclModule =>
      exact .contextFree (.wrapped (by apply exportDeclModule_case))
  | exportDeclAliased =>
      exact .contextFree (.wrapped (by
        apply exportDeclAliased_case <;> assumption))
  | exportDeclWildcard =>
      exact .endpoint (by apply EndpointSensitiveRuleCase.exportDeclWildcard)
  | exportDeclBraced =>
      exact .endpoint (by apply EndpointSensitiveRuleCase.exportDeclBraced)
  | localExportEntryWildcard =>
      exact .contextFree (.wrapped (by apply localExportEntryWildcard_case))
  | localExportEntryItem =>
      exact .contextFree (.wrapped (by apply localExportEntryItem_case))
  | localExportEntryAllFrom =>
      exact .contextFree (.wrapped (by apply localExportEntryAllFrom_case))
  | remoteExportEntryWildcard =>
      exact .contextFree (.wrapped (by apply remoteExportEntryWildcard_case))
  | remoteExportEntryItem =>
      exact .contextFree (.wrapped (by apply remoteExportEntryItem_case))
  | exportItem =>
      exact .contextFree (.wrapped (by
        apply exportItem_case <;> assumption))
  | constructorSelectionAll =>
      exact .contextFree (.wrapped (by apply constructorSelectionAll_case))
  | constructorSelectionNamed =>
      exact .contextFree (.wrapped (by
        apply constructorSelectionNamed_case <;> assumption))
  | pragmaDeclNoCoverageCondition =>
      exact .contextFree (.wrapped (by
        apply pragmaDeclNoCoverageCondition_case <;> assumption))
  | pragmaDeclNoPattersonCondition =>
      exact .contextFree (.wrapped (by
        apply pragmaDeclNoPattersonCondition_case <;> assumption))
  | pragmaDeclNoBoundedVariableCondition =>
      exact .contextFree (.wrapped (by
        apply pragmaDeclNoBoundedVariableCondition_case <;> assumption))
  | pragmaDeclNoGenericInstanceFor =>
      exact .contextFree (.wrapped (by
        apply pragmaDeclNoGenericInstanceFor_case <;> assumption))
  | genericPrefixBare =>
      exact .contextFree (.wrapped (by apply genericPrefixBare_case))
  | genericPrefixContext =>
      exact .contextFree (.wrapped (by apply genericPrefixContext_case))
  | forallClause =>
      exact .contextFree (.wrapped (by apply forallClause_case))
  | forallBinderBare =>
      exact .contextFree (.wrapped (by
        apply forallBinderBare_case <;> assumption))
  | forallBinderBoundedWithoutArguments =>
      exact .contextFree (.wrapped (by
        apply forallBinderBoundedWithoutArguments_case <;> assumption))
  | forallBinderBoundedWithArguments =>
      exact .contextFree (.wrapped (by
        apply forallBinderBoundedWithArguments_case <;> assumption))
  | optionalCommaAbsent =>
      exact .contextFree (.exact (.exactResult (by apply ExactResult.optionalCommaAbsent)))
  | optionalCommaPresent =>
      exact .contextFree (.exact (.exactResult (by apply ExactResult.optionalCommaPresent)))
  | predicateList =>
      exact .contextFree (.exact (.exactResult (by apply ExactResult.predicateList)))
  | predicateWithoutArguments =>
      exact .contextFree (.wrapped (by
        apply predicateWithoutArguments_case <;> assumption))
  | predicateWithArguments =>
      exact .contextFree (.wrapped (by
        apply predicateWithArguments_case <;> assumption))
  | functionSignature =>
      exact .contextFree (.wrapped (by
        apply functionSignature_case <;> assumption))
  | functionDecl =>
      exact .contextFree (.wrapped (by apply functionDecl_case))
  | classMethod =>
      exact .contextFree (.wrapped (by apply classMethod_case))
  | dataDecl =>
      exact .contextFree (.wrapped (by
        apply dataDecl_case <;> assumption))
  | dataConstructorWithoutArguments =>
      exact .contextFree (.wrapped (by
        apply dataConstructorWithoutArguments_case <;> assumption))
  | dataConstructorWithArguments =>
      exact .contextFree (.wrapped (by
        apply dataConstructorWithArguments_case <;> assumption))
  | typeAliasDecl =>
      exact .contextFree (.wrapped (by
        apply typeAliasDecl_case <;> assumption))
  | classDecl =>
      exact .contextFree (.wrapped (by
        apply classDecl_case <;> assumption))
  | instanceDecl =>
      exact .contextFree (.wrapped (by
        apply instanceDecl_case <;> assumption))
  | instanceMethod =>
      exact .contextFree (.exact (.semanticPassThrough (by
        apply SemanticPassThrough.instanceMethod)))
  | contractDecl =>
      exact .contextFree (.wrapped (by
        apply contractDecl_case <;> assumption))
  | contractMemberData =>
      exact .contextFree (.wrapped (by apply contractMemberData_case))
  | contractMemberTypeAlias =>
      exact .contextFree (.wrapped (by apply contractMemberTypeAlias_case))
  | contractMemberField =>
      exact .contextFree (.wrapped (by apply contractMemberField_case))
  | contractMemberFunction =>
      exact .contextFree (.wrapped (by apply contractMemberFunction_case))
  | contractMemberFallback =>
      exact .contextFree (.wrapped (by apply contractMemberFallback_case))
  | contractMemberConstructor =>
      exact .contextFree (.wrapped (by apply contractMemberConstructor_case))
  | fieldDecl =>
      exact .contextFree (.wrapped (by
        apply fieldDecl_case <;> assumption))
  | fallbackDecl =>
      exact .contextFree (.wrapped (by
        apply fallbackDecl_case <;> assumption))
  | contractConstructorDecl =>
      exact .contextFree (.wrapped (by
        apply contractConstructorDecl_case <;> assumption))
  | parameter =>
      exact .contextFree (.wrapped (by
        apply parameter_case <;> assumption))
  | body =>
      exact .contextFree (.wrapped (by apply body_case))
  | typeComptime =>
      exact .contextFree (.wrapped (by apply typeComptime_case))
  | typeAtomOnly =>
      exact .contextFree (.exact (.semanticPassThrough (by
        apply SemanticPassThrough.typeAtomOnly)))
  | typeFunction =>
      exact .contextFree (.wrapped (by apply typeFunction_case))
  | typeAtomProxy =>
      exact .contextFree (.wrapped (by apply typeAtomProxy_case))
  | typeAtomNamedWithoutArguments =>
      exact .contextFree (.wrapped (by apply typeAtomNamedWithoutArguments_case))
  | typeAtomNamedWithArguments =>
      exact .contextFree (.wrapped (by
        apply typeAtomNamedWithArguments_case <;> assumption))
  | typeAtomEmptyTuple =>
      exact .contextFree (.wrapped (by apply typeAtomEmptyTuple_case))
  | typeAtomGroup =>
      exact .contextFree (.wrapped (by apply typeAtomGroup_case))
  | typeAtomTuple =>
      exact .contextFree (.wrapped (by apply typeAtomTuple_case))
  | qualifiedName =>
      exact .contextFree (.wrapped (by
        apply qualifiedName_case <;> assumption))
  | statementLet =>
      exact .contextFree (.exact (.semanticPassThrough (by
        apply SemanticPassThrough.statementLet)))
  | statementReturn =>
      exact .contextFree (.exact (.semanticPassThrough (by
        apply SemanticPassThrough.statementReturn)))
  | statementMatch =>
      exact .contextFree (.exact (.semanticPassThrough (by
        apply SemanticPassThrough.statementMatch)))
  | statementIf =>
      exact .contextFree (.exact (.semanticPassThrough (by
        apply SemanticPassThrough.statementIf)))
  | statementFor =>
      exact .contextFree (.exact (.semanticPassThrough (by
        apply SemanticPassThrough.statementFor)))
  | statementAssembly =>
      exact .contextFree (.exact (.semanticPassThrough (by
        apply SemanticPassThrough.statementAssembly)))
  | statementBlock =>
      exact .contextFree (.exact (.semanticPassThrough (by
        apply SemanticPassThrough.statementBlock)))
  | statementBreak =>
      exact .contextFree (.exact (.semanticPassThrough (by
        apply SemanticPassThrough.statementBreak)))
  | statementContinue =>
      exact .contextFree (.exact (.semanticPassThrough (by
        apply SemanticPassThrough.statementContinue)))
  | statementAssignment =>
      exact .contextFree (.exact (.semanticPassThrough (by
        apply SemanticPassThrough.statementAssignment)))
  | statementExpression =>
      exact .contextFree (.exact (.semanticPassThrough (by
        apply SemanticPassThrough.statementExpression)))
  | letStatement =>
      exact .contextFree (.wrapped (by apply letStatement_case))
  | letBindingUntyped =>
      exact .contextFree (.wrapped (by
        apply letBindingUntyped_case <;> assumption))
  | letBindingTyped =>
      exact .contextFree (.wrapped (by
        apply letBindingTyped_case <;> assumption))
  | letBindingComptime =>
      exact .contextFree (.wrapped (by
        apply letBindingComptime_case <;> assumption))
  | returnStatement =>
      exact .contextFree (.wrapped (by apply returnStatement_case))
  | blockStatement =>
      exact .contextFree (.wrapped (by apply blockStatement_case))
  | breakStatement =>
      exact .contextFree (.wrapped (by apply breakStatement_case))
  | continueStatement =>
      exact .contextFree (.wrapped (by apply continueStatement_case))
  | assemblyStatement =>
      exact .contextFree (.assembly _)
  | ifStatementWithoutElse =>
      exact .contextFree (.wrapped (by apply ifStatementWithoutElse_case))
  | ifStatementWithElse =>
      exact .contextFree (.wrapped (by apply ifStatementWithElse_case))
  | forStatement =>
      exact .contextFree (.wrapped (by apply forStatement_case))
  | forInitItemLet =>
      exact .contextFree (.wrapped (by apply forInitItemLet_case))
  | forInitItemAssignment =>
      exact .contextFree (.wrapped (by apply forInitItemAssignment_case))
  | forInitItemExpression =>
      exact .contextFree (.wrapped (by apply forInitItemExpression_case))
  | forPostItemAssignment =>
      exact .contextFree (.wrapped (by apply forPostItemAssignment_case))
  | forPostItemExpression =>
      exact .contextFree (.wrapped (by apply forPostItemExpression_case))
  | matchStatement =>
      exact .contextFree (.wrapped (by apply matchStatement_case))
  | matchArm =>
      exact .endpoint (.matchArm _)
  | armStatement =>
      exact .contextFree (.exact (.semanticPassThrough (by
        apply SemanticPassThrough.armStatement)))
  | assignmentStatement =>
      exact .contextFree (.wrapped (by apply assignmentStatement_case))
  | assignmentOperatorEqual =>
      exact .contextFree (.exact (.exactResult (by apply ExactResult.assignmentOperatorEqual)))
  | assignmentOperatorAddEqual =>
      exact .contextFree (.exact (.exactResult (by apply ExactResult.assignmentOperatorAddEqual)))
  | assignmentOperatorSubtractEqual =>
      exact .contextFree (.exact (.exactResult (by apply ExactResult.assignmentOperatorSubtractEqual)))
  | assignmentOperatorBitXorEqual =>
      exact .contextFree (.exact (.exactResult (by apply ExactResult.assignmentOperatorBitXorEqual)))
  | assignmentOperatorBitAndEqual =>
      exact .contextFree (.exact (.exactResult (by apply ExactResult.assignmentOperatorBitAndEqual)))
  | assignmentOperatorBitOrEqual =>
      exact .contextFree (.exact (.exactResult (by apply ExactResult.assignmentOperatorBitOrEqual)))
  | assignmentOperatorModuloEqual =>
      exact .contextFree (.exact (.exactResult (by apply ExactResult.assignmentOperatorModuloEqual)))
  | expressionStatementTerminated =>
      exact .contextFree (.wrapped (by apply expressionStatementTerminated_case))
  | expressionStatementTerminal =>
      exact .contextFree (.wrapped (by apply expressionStatementTerminal_case))
  | terminalExpression =>
      exact .contextFree (.exact (.semanticPassThrough (by
        apply SemanticPassThrough.terminalExpression)))
  | patternWildcard =>
      exact .contextFree (.wrapped (by apply patternWildcard_case))
  | patternLiteral =>
      exact .contextFree (.wrapped (by apply patternLiteral_case))
  | patternDotConstructorWithoutArguments =>
      exact .contextFree (.wrapped (by
        apply patternDotConstructorWithoutArguments_case <;> assumption))
  | patternDotConstructorWithArguments =>
      exact .contextFree (.wrapped (by
        apply patternDotConstructorWithArguments_case <;> assumption))
  | patternComptime =>
      exact .contextFree (.wrapped (by apply patternComptime_case))
  | patternNamedWithoutArguments =>
      exact .contextFree (.wrapped (by apply patternNamedWithoutArguments_case))
  | patternNamedWithArguments =>
      exact .contextFree (.wrapped (by apply patternNamedWithArguments_case))
  | patternEmptyTuple =>
      exact .contextFree (.wrapped (by apply patternEmptyTuple_case))
  | patternGroup =>
      exact .contextFree (.wrapped (by apply patternGroup_case))
  | patternTuple =>
      exact .contextFree (.wrapped (by apply patternTuple_case))
  | expression =>
      exact .contextFree (.exact (.semanticPassThrough (by
        apply SemanticPassThrough.expression)))
  | annotationNone =>
      exact .contextFree (.exact (.semanticPassThrough (by
        apply SemanticPassThrough.annotationNone)))
  | annotationSome =>
      exact .contextFree (.wrapped (by apply annotationSome_case))
  | conditionalKeyword =>
      exact .contextFree (.wrapped (by apply conditionalKeyword_case))
  | conditionalLogical =>
      exact .contextFree (.exact (.semanticPassThrough (by
        apply SemanticPassThrough.conditionalLogical)))
  | conditionalTernary =>
      exact .contextFree (.wrapped (by apply conditionalTernary_case))
  | logicalOr =>
      exact .endpoint (.logicalOr _)
  | logicalAnd =>
      exact .endpoint (.logicalAnd _)
  | equalityNone =>
      exact .contextFree (.exact (.semanticPassThrough (by
        apply SemanticPassThrough.equalityNone)))
  | equalityEqual =>
      exact .contextFree (.wrapped (by apply equalityEqual_case))
  | equalityNotEqual =>
      exact .contextFree (.wrapped (by apply equalityNotEqual_case))
  | relationalNone =>
      exact .contextFree (.exact (.semanticPassThrough (by
        apply SemanticPassThrough.relationalNone)))
  | relationalLess =>
      exact .contextFree (.wrapped (by apply relationalLess_case))
  | relationalGreater =>
      exact .contextFree (.wrapped (by apply relationalGreater_case))
  | relationalLessEqual =>
      exact .contextFree (.wrapped (by apply relationalLessEqual_case))
  | relationalGreaterEqual =>
      exact .contextFree (.wrapped (by apply relationalGreaterEqual_case))
  | bitOr =>
      exact .endpoint (.bitOr _)
  | bitXor =>
      exact .endpoint (.bitXor _)
  | bitAnd =>
      exact .endpoint (.bitAnd _)
  | additive =>
      exact .endpoint (.additive _)
  | multiplicative =>
      exact .endpoint (.multiplicative _)
  | prefixLogicalNot =>
      exact .contextFree (.wrapped (by apply prefixLogicalNot_case))
  | prefixPostfix =>
      exact .contextFree (.exact (.semanticPassThrough (by
        apply SemanticPassThrough.prefixPostfix)))
  | «postfix» =>
      exact .endpoint (.postfix _)
  | postfixPartCall =>
      exact .contextFree (.exact (.exactResult (by apply ExactResult.postfixPartCall)))
  | postfixPartSelect =>
      exact .contextFree (.exact (.exactResult (by
        apply ExactResult.postfixPartSelect <;> assumption)))
  | postfixPartIndex =>
      exact .contextFree (.exact (.exactResult (by apply ExactResult.postfixPartIndex)))
  | atomLiteral =>
      exact .contextFree (.wrapped (by apply atomLiteral_case))
  | atomName =>
      exact .contextFree (.wrapped (by
        apply atomName_case <;> assumption))
  | atomDotConstructorWithoutArguments =>
      exact .contextFree (.wrapped (by
        apply atomDotConstructorWithoutArguments_case <;> assumption))
  | atomDotConstructorWithArguments =>
      exact .contextFree (.wrapped (by
        apply atomDotConstructorWithArguments_case <;> assumption))
  | atomProxy =>
      exact .contextFree (.wrapped (by apply atomProxy_case))
  | atomLambda =>
      exact .contextFree (.exact (.semanticPassThrough (by
        apply SemanticPassThrough.atomLambda)))
  | atomEmptyTuple =>
      exact .contextFree (.wrapped (by apply atomEmptyTuple_case))
  | atomGroup =>
      exact .contextFree (.wrapped (by apply atomGroup_case))
  | atomTuple =>
      exact .contextFree (.wrapped (by apply atomTuple_case))
  | lambda =>
      exact .contextFree (.wrapped (by apply lambda_case))
  | literalDecimal =>
      exact .contextFree (.exact (.exactResult (by
        apply ExactResult.literalDecimal <;> assumption)))
  | literalHexadecimal =>
      exact .contextFree (.exact (.exactResult (by
        apply ExactResult.literalHexadecimal <;> assumption)))
  | literalString =>
      exact .contextFree (.exact (.exactResult (by
        apply ExactResult.literalString <;> assumption)))

end RuleReduction

end Solcore.Surface.Multi
