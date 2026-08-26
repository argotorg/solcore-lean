import Solcore.Surface.Multi.RuleIntervalLocation

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar
open Solcore.Workspace

namespace RuleReduction

/-- The 47 reductions whose complete input fragment is the payload of one
new checked source wrapper.  This finite registry keeps the intended coverage
auditable independently of the proof objects below. -/
inductive ExactWrappedLocationCase where
  | topItemImport
  | topItemExport
  | topItemPragma
  | topItemData
  | topItemTypeAlias
  | topItemClass
  | topItemInstance
  | topItemContract
  | topItemFunction
  | moduleRefRelativeLibraryEmpty
  | importEntryWildcard
  | importEntryNamed
  | localExportEntryWildcard
  | localExportEntryItem
  | remoteExportEntryWildcard
  | remoteExportEntryItem
  | exportItem
  | genericPrefixBare
  | forallBinderBare
  | functionDecl
  | classMethod
  | dataConstructorWithoutArguments
  | contractMemberData
  | contractMemberTypeAlias
  | contractMemberField
  | contractMemberFunction
  | contractMemberFallback
  | contractMemberConstructor
  | typeComptime
  | typeAtomProxy
  | typeAtomNamedWithoutArguments
  | blockStatement
  | forInitItemLet
  | forInitItemExpression
  | forPostItemExpression
  | expressionStatementTerminated
  | expressionStatementTerminal
  | patternWildcard
  | patternLiteral
  | patternDotConstructorWithoutArguments
  | patternComptime
  | patternNamedWithoutArguments
  | prefixLogicalNot
  | atomLiteral
  | atomName
  | atomDotConstructorWithoutArguments
  | atomProxy
  deriving DecidableEq, Repr

/-- The 74 reductions that select or reorder input locations before adding one
checked source wrapper. -/
inductive ProjectedWrappedLocationCase where
  | moduleRefExternal
  | moduleRefStandard
  | moduleRefLibraryRoot
  | moduleRefRelativeOther
  | importDeclModule
  | importDeclAliased
  | importEntryAliased
  | hidingClause
  | exportDeclModule
  | exportDeclAliased
  | localExportEntryAllFrom
  | constructorSelectionAll
  | constructorSelectionNamed
  | pragmaDeclNoCoverageCondition
  | pragmaDeclNoPattersonCondition
  | pragmaDeclNoBoundedVariableCondition
  | pragmaDeclNoGenericInstanceFor
  | genericPrefixContext
  | forallClause
  | forallBinderBoundedWithoutArguments
  | forallBinderBoundedWithArguments
  | predicateWithoutArguments
  | predicateWithArguments
  | functionSignature
  | dataDecl
  | dataConstructorWithArguments
  | typeAliasDecl
  | classDecl
  | instanceDecl
  | contractDecl
  | fieldDecl
  | fallbackDecl
  | contractConstructorDecl
  | parameter
  | body
  | typeFunction
  | typeAtomNamedWithArguments
  | typeAtomEmptyTuple
  | typeAtomGroup
  | typeAtomTuple
  | qualifiedName
  | letStatement
  | letBindingUntyped
  | letBindingTyped
  | letBindingComptime
  | returnStatement
  | breakStatement
  | continueStatement
  | ifStatementWithoutElse
  | ifStatementWithElse
  | forStatement
  | forInitItemAssignment
  | forPostItemAssignment
  | matchStatement
  | assignmentStatement
  | patternDotConstructorWithArguments
  | patternNamedWithArguments
  | patternEmptyTuple
  | patternGroup
  | patternTuple
  | annotationSome
  | conditionalKeyword
  | conditionalTernary
  | equalityEqual
  | equalityNotEqual
  | relationalLess
  | relationalGreater
  | relationalLessEqual
  | relationalGreaterEqual
  | atomDotConstructorWithArguments
  | atomEmptyTuple
  | atomGroup
  | atomTuple
  | lambda
  deriving DecidableEq, Repr

namespace ExactWrappedLocationCase

/-- Exhaustive registry in source-rule declaration order. -/
def all : List ExactWrappedLocationCase := [
  .topItemImport,
  .topItemExport,
  .topItemPragma,
  .topItemData,
  .topItemTypeAlias,
  .topItemClass,
  .topItemInstance,
  .topItemContract,
  .topItemFunction,
  .moduleRefRelativeLibraryEmpty,
  .importEntryWildcard,
  .importEntryNamed,
  .localExportEntryWildcard,
  .localExportEntryItem,
  .remoteExportEntryWildcard,
  .remoteExportEntryItem,
  .exportItem,
  .genericPrefixBare,
  .forallBinderBare,
  .functionDecl,
  .classMethod,
  .dataConstructorWithoutArguments,
  .contractMemberData,
  .contractMemberTypeAlias,
  .contractMemberField,
  .contractMemberFunction,
  .contractMemberFallback,
  .contractMemberConstructor,
  .typeComptime,
  .typeAtomProxy,
  .typeAtomNamedWithoutArguments,
  .blockStatement,
  .forInitItemLet,
  .forInitItemExpression,
  .forPostItemExpression,
  .expressionStatementTerminated,
  .expressionStatementTerminal,
  .patternWildcard,
  .patternLiteral,
  .patternDotConstructorWithoutArguments,
  .patternComptime,
  .patternNamedWithoutArguments,
  .prefixLogicalNot,
  .atomLiteral,
  .atomName,
  .atomDotConstructorWithoutArguments,
  .atomProxy
]

@[simp] theorem all_length : all.length = 47 := by
  rfl

theorem mem_all (locationCase : ExactWrappedLocationCase) :
    locationCase ∈ all := by
  cases locationCase <;> simp [all]

theorem all_nodup : all.Nodup := by
  simp [all]

end ExactWrappedLocationCase

namespace ProjectedWrappedLocationCase

/-- Exhaustive registry in source-rule declaration order. -/
def all : List ProjectedWrappedLocationCase := [
  .moduleRefExternal,
  .moduleRefStandard,
  .moduleRefLibraryRoot,
  .moduleRefRelativeOther,
  .importDeclModule,
  .importDeclAliased,
  .importEntryAliased,
  .hidingClause,
  .exportDeclModule,
  .exportDeclAliased,
  .localExportEntryAllFrom,
  .constructorSelectionAll,
  .constructorSelectionNamed,
  .pragmaDeclNoCoverageCondition,
  .pragmaDeclNoPattersonCondition,
  .pragmaDeclNoBoundedVariableCondition,
  .pragmaDeclNoGenericInstanceFor,
  .genericPrefixContext,
  .forallClause,
  .forallBinderBoundedWithoutArguments,
  .forallBinderBoundedWithArguments,
  .predicateWithoutArguments,
  .predicateWithArguments,
  .functionSignature,
  .dataDecl,
  .dataConstructorWithArguments,
  .typeAliasDecl,
  .classDecl,
  .instanceDecl,
  .contractDecl,
  .fieldDecl,
  .fallbackDecl,
  .contractConstructorDecl,
  .parameter,
  .body,
  .typeFunction,
  .typeAtomNamedWithArguments,
  .typeAtomEmptyTuple,
  .typeAtomGroup,
  .typeAtomTuple,
  .qualifiedName,
  .letStatement,
  .letBindingUntyped,
  .letBindingTyped,
  .letBindingComptime,
  .returnStatement,
  .breakStatement,
  .continueStatement,
  .ifStatementWithoutElse,
  .ifStatementWithElse,
  .forStatement,
  .forInitItemAssignment,
  .forPostItemAssignment,
  .matchStatement,
  .assignmentStatement,
  .patternDotConstructorWithArguments,
  .patternNamedWithArguments,
  .patternEmptyTuple,
  .patternGroup,
  .patternTuple,
  .annotationSome,
  .conditionalKeyword,
  .conditionalTernary,
  .equalityEqual,
  .equalityNotEqual,
  .relationalLess,
  .relationalGreater,
  .relationalLessEqual,
  .relationalGreaterEqual,
  .atomDotConstructorWithArguments,
  .atomEmptyTuple,
  .atomGroup,
  .atomTuple,
  .lambda
]

@[simp] theorem all_length : all.length = 74 := by
  rfl

theorem mem_all (locationCase : ProjectedWrappedLocationCase) :
    locationCase ∈ all := by
  cases locationCase <;> simp [all]

theorem all_nodup : all.Nodup := by
  simp [all]

/-- Precisely the projected cases whose retained core can have no roots. -/
def allowsEmptyCore : ProjectedWrappedLocationCase → Bool
  | .hidingClause
  | .typeAtomEmptyTuple
  | .patternEmptyTuple
  | .atomEmptyTuple => true
  | _ => false

@[simp] theorem empty_core_count :
    (all.filter allowsEmptyCore).length = 4 := by
  rfl

theorem allowsEmptyCore_eq_true_iff
    (locationCase : ProjectedWrappedLocationCase) :
    allowsEmptyCore locationCase = true ↔
      locationCase = .hidingClause ∨
      locationCase = .typeAtomEmptyTuple ∨
      locationCase = .patternEmptyTuple ∨
      locationCase = .atomEmptyTuple := by
  cases locationCase <;> simp [allowsEmptyCore]

end ProjectedWrappedLocationCase

@[simp] theorem wrapped_location_case_count :
    ExactWrappedLocationCase.all.length +
      ProjectedWrappedLocationCase.all.length = 121 := by
  rfl

/-- A source-rule action adds exactly one checked outer source location.  The
payload may either be the whole input fragment or a projection/permutation of
it.  Occupancy is recorded for the original input, deliberately before a
possibly-empty projection is selected. -/
inductive WrappedLocation
    {file : WorkspaceFile} {tokens : List Token}
    {rule : GrammarRuleId} {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs rule)}
    {output : RuleValue rule}
    (_reduces : RuleReduction file tokens rule origin finish input output) :
    Prop where
  | exactInput
      (witness : ConsumedSpanWitness file tokens origin finish)
      (outputLocation :
        RuleLocationView.ofRuleValue rule output =
          LocationFragment.located witness.span [input.locationFragment])
      (inputOccupied : input.locationFragment.roots ≠ []) :
      WrappedLocation _reduces
  | projectedInput
      (witness : ConsumedSpanWitness file tokens origin finish)
      (core : LocationFragment)
      (outputLocation :
        RuleLocationView.ofRuleValue rule output =
          LocationFragment.located witness.span [core])
      (coreFromInput : core.IsSubfragmentOf input.locationFragment)
      (inputOccupied : input.locationFragment.roots ≠ []) :
      WrappedLocation _reduces

namespace WrappedLocation

/-- The exact-input case is the reflexive instance of the general projected
case. -/
theorem coreShape
    {file : WorkspaceFile} {tokens : List Token}
    {rule : GrammarRuleId} {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs rule)}
    {output : RuleValue rule}
    {reduces : RuleReduction file tokens rule origin finish input output}
    (wrapped : WrappedLocation reduces) :
    ∃ witness : ConsumedSpanWitness file tokens origin finish,
      ∃ core : LocationFragment,
        RuleLocationView.ofRuleValue rule output =
            LocationFragment.located witness.span [core] ∧
          core.IsSubfragmentOf input.locationFragment ∧
          input.locationFragment.roots ≠ [] := by
  cases wrapped with
  | exactInput witness outputLocation inputOccupied =>
      exact ⟨witness, input.locationFragment, outputLocation,
        LocationFragment.IsSubfragmentOf.refl _, inputOccupied⟩
  | projectedInput witness core outputLocation coreFromInput inputOccupied =>
      exact ⟨witness, core, outputLocation, coreFromInput, inputOccupied⟩

/-- Every classified outer-wrapper action preserves the complete physical
trace and produces valid, nested semantic interval evidence. -/
theorem locationSound
    {file : WorkspaceFile} {tokens : List Token}
    (tokensOrdered : TokenSpansOrdered tokens)
    {rule : GrammarRuleId} {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs rule)}
    {output : RuleValue rule}
    {reduces : RuleReduction file tokens rule origin finish input output}
    (wrapped : WrappedLocation reduces) :
    RuleReduction.LocationSound reduces := by
  intro trace evidence
  rcases wrapped.coreShape with
    ⟨witness, core, outputLocation, coreFromInput, inputOccupied⟩
  rw [outputLocation]
  exact IntervalLocationEvidence.restrictAndLocateByWitness
    tokensOrdered witness coreFromInput evidence inputOccupied

/-- Direct form for exact-input wrapper cases. -/
theorem exactInput_locationSound
    {file : WorkspaceFile} {tokens : List Token}
    (tokensOrdered : TokenSpansOrdered tokens)
    {rule : GrammarRuleId} {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs rule)}
    {output : RuleValue rule}
    {reduces : RuleReduction file tokens rule origin finish input output}
    (witness : ConsumedSpanWitness file tokens origin finish)
    (outputLocation :
      RuleLocationView.ofRuleValue rule output =
        LocationFragment.located witness.span [input.locationFragment])
    (inputOccupied : input.locationFragment.roots ≠ []) :
    RuleReduction.LocationSound reduces :=
  locationSound tokensOrdered
    (WrappedLocation.exactInput witness outputLocation inputOccupied)

/-- Direct form for projected or permuted wrapper cases. -/
theorem projectedInput_locationSound
    {file : WorkspaceFile} {tokens : List Token}
    (tokensOrdered : TokenSpansOrdered tokens)
    {rule : GrammarRuleId} {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs rule)}
    {output : RuleValue rule}
    {reduces : RuleReduction file tokens rule origin finish input output}
    (witness : ConsumedSpanWitness file tokens origin finish)
    (core : LocationFragment)
    (outputLocation :
      RuleLocationView.ofRuleValue rule output =
        LocationFragment.located witness.span [core])
    (coreFromInput : core.IsSubfragmentOf input.locationFragment)
    (inputOccupied : input.locationFragment.roots ≠ []) :
    RuleReduction.LocationSound reduces :=
  locationSound tokensOrdered
    (WrappedLocation.projectedInput witness core outputLocation
      coreFromInput inputOccupied)

/-- Empty projections remain sound because occupancy comes from the complete
input fragment rather than from the retained core. -/
theorem emptyCore_locationSound
    {file : WorkspaceFile} {tokens : List Token}
    (tokensOrdered : TokenSpansOrdered tokens)
    {rule : GrammarRuleId} {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs rule)}
    {output : RuleValue rule}
    {reduces : RuleReduction file tokens rule origin finish input output}
    (witness : ConsumedSpanWitness file tokens origin finish)
    (outputLocation :
      RuleLocationView.ofRuleValue rule output =
        LocationFragment.located witness.span [LocationFragment.empty])
    (inputOccupied : input.locationFragment.roots ≠ []) :
    RuleReduction.LocationSound reduces := by
  apply projectedInput_locationSound tokensOrdered witness
      LocationFragment.empty outputLocation
  · exact ⟨by simp, by simp, by simp⟩
  · exact inputOccupied

end WrappedLocation

end RuleReduction

end Solcore.Surface.Multi
