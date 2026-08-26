import Solcore.Surface.Multi.RuleIntervalLocationWrapped
import Solcore.Surface.Multi.EbnfLocationSubfragment

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar
open Solcore.Workspace

namespace RuleReduction.WrappedLocation

/-! Concrete proofs for source-rule reductions that add one checked outer
location wrapper.  Cases are kept separate so the final dispatcher remains
auditable against `RuleReduction`. -/

private def InputFragmentEquals
    {file : WorkspaceFile} {tokens : List Token}
    {rule : GrammarRuleId} {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs rule)}
    {output : RuleValue rule}
    (_reduces : RuleReduction file tokens rule origin finish input output)
    (core : LocationFragment) : Prop :=
  input.locationFragment = core

private theorem exactInput_of_shape
    {file : WorkspaceFile} {tokens : List Token}
    {rule : GrammarRuleId} {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs rule)}
    {output : RuleValue rule}
    {reduces : RuleReduction file tokens rule origin finish input output}
    (witness : ConsumedSpanWitness file tokens origin finish)
    (core : LocationFragment)
    (inputShape : InputFragmentEquals reduces core)
    (outputShape : RuleLocationView.ofRuleValue rule output =
      LocationFragment.located witness.span [core])
    (coreOccupied : core.roots ≠ []) :
    WrappedLocation reduces := by
  unfold InputFragmentEquals at inputShape
  apply WrappedLocation.exactInput witness
  · rw [inputShape]
    exact outputShape
  · rw [inputShape]
    exact coreOccupied

theorem topItemImport_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens) (declaration : ImportDecl)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.topItemImport origin finish declaration witness) := by
  apply exactInput_of_shape witness
      (LocationFragment.ofImportDecl declaration)
  · unfold InputFragmentEquals
    exact (EbnfValue.locationFragment_transport _ _).trans
      ((EbnfValue.locationFragment_choice _ _).trans
        (EbnfValue.locationFragment_ruleAtom _ _))
  · change LocationFragment.located witness.span
      [LocationFragment.ofImportDecl declaration] = _
    rfl
  · simp

theorem topItemExport_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens) (declaration : ExportDecl)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.topItemExport origin finish declaration witness) := by
  apply exactInput_of_shape witness
      (LocationFragment.ofExportDecl declaration)
  · unfold InputFragmentEquals
    exact (EbnfValue.locationFragment_transport _ _).trans
      ((EbnfValue.locationFragment_choice _ _).trans
        (EbnfValue.locationFragment_ruleAtom _ _))
  · change LocationFragment.located witness.span
      [LocationFragment.ofExportDecl declaration] = _
    rfl
  · simp

theorem topItemPragma_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens) (declaration : PragmaDecl)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.topItemPragma origin finish declaration witness) := by
  apply exactInput_of_shape witness
      (LocationFragment.ofPragmaDecl declaration)
  · unfold InputFragmentEquals
    exact (EbnfValue.locationFragment_transport _ _).trans
      ((EbnfValue.locationFragment_choice _ _).trans
        (EbnfValue.locationFragment_ruleAtom _ _))
  · change LocationFragment.located witness.span
      [LocationFragment.ofPragmaDecl declaration] = _
    rfl
  · simp

theorem topItemData_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens) (declaration : DataDecl)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.topItemData origin finish declaration witness) := by
  apply exactInput_of_shape witness
      (LocationFragment.ofDataDecl declaration)
  · unfold InputFragmentEquals
    exact (EbnfValue.locationFragment_transport _ _).trans
      ((EbnfValue.locationFragment_choice _ _).trans
        (EbnfValue.locationFragment_ruleAtom _ _))
  · change LocationFragment.located witness.span
      [LocationFragment.ofDataDecl declaration] = _
    rfl
  · simp

theorem topItemTypeAlias_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens) (declaration : TypeAliasDecl)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.topItemTypeAlias origin finish declaration witness) := by
  apply exactInput_of_shape witness
      (LocationFragment.ofTypeAliasDecl declaration)
  · unfold InputFragmentEquals
    exact (EbnfValue.locationFragment_transport _ _).trans
      ((EbnfValue.locationFragment_choice _ _).trans
        (EbnfValue.locationFragment_ruleAtom _ _))
  · change LocationFragment.located witness.span
      [LocationFragment.ofTypeAliasDecl declaration] = _
    rfl
  · simp

theorem topItemClass_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens) (declaration : ClassDecl)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.topItemClass origin finish declaration witness) := by
  apply exactInput_of_shape witness
      (LocationFragment.ofClassDecl declaration)
  · unfold InputFragmentEquals
    exact (EbnfValue.locationFragment_transport _ _).trans
      ((EbnfValue.locationFragment_choice _ _).trans
        (EbnfValue.locationFragment_ruleAtom _ _))
  · change LocationFragment.located witness.span
      [LocationFragment.ofClassDecl declaration] = _
    rfl
  · simp

theorem topItemInstance_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens) (declaration : InstanceDecl)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.topItemInstance origin finish declaration witness) := by
  apply exactInput_of_shape witness
      (LocationFragment.ofInstanceDecl declaration)
  · unfold InputFragmentEquals
    exact (EbnfValue.locationFragment_transport _ _).trans
      ((EbnfValue.locationFragment_choice _ _).trans
        (EbnfValue.locationFragment_ruleAtom _ _))
  · change LocationFragment.located witness.span
      [LocationFragment.ofInstanceDecl declaration] = _
    rfl
  · simp

theorem topItemContract_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens) (declaration : ContractDecl)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.topItemContract origin finish declaration witness) := by
  apply exactInput_of_shape witness
      (LocationFragment.ofContractDecl declaration)
  · unfold InputFragmentEquals
    exact (EbnfValue.locationFragment_transport _ _).trans
      ((EbnfValue.locationFragment_choice _ _).trans
        (EbnfValue.locationFragment_ruleAtom _ _))
  · change LocationFragment.located witness.span
      [LocationFragment.ofContractDecl declaration] = _
    rfl
  · simp

theorem topItemFunction_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens) (declaration : FunctionDecl)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.topItemFunction origin finish declaration witness) := by
  apply exactInput_of_shape witness
      (LocationFragment.ofFunctionDecl declaration)
  · unfold InputFragmentEquals
    exact (EbnfValue.locationFragment_transport _ _).trans
      ((EbnfValue.locationFragment_choice _ _).trans
        (EbnfValue.locationFragment_ruleAtom _ _))
  · change LocationFragment.located witness.span
      [LocationFragment.ofFunctionDecl declaration] = _
    rfl
  · simp

theorem contractMemberData_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens) (declaration : DataDecl)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.contractMemberData origin finish declaration
        witness) := by
  apply exactInput_of_shape witness
      (LocationFragment.ofDataDecl declaration)
  · unfold InputFragmentEquals
    exact (EbnfValue.locationFragment_transport _ _).trans
      ((EbnfValue.locationFragment_choice _ _).trans
        (EbnfValue.locationFragment_ruleAtom _ _))
  · change LocationFragment.located witness.span
      [LocationFragment.ofDataDecl declaration] = _
    rfl
  · simp

theorem contractMemberTypeAlias_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens) (declaration : TypeAliasDecl)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.contractMemberTypeAlias origin finish declaration
        witness) := by
  apply exactInput_of_shape witness
      (LocationFragment.ofTypeAliasDecl declaration)
  · unfold InputFragmentEquals
    exact (EbnfValue.locationFragment_transport _ _).trans
      ((EbnfValue.locationFragment_choice _ _).trans
        (EbnfValue.locationFragment_ruleAtom _ _))
  · change LocationFragment.located witness.span
      [LocationFragment.ofTypeAliasDecl declaration] = _
    rfl
  · simp

theorem contractMemberField_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens) (declaration : FieldDecl)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.contractMemberField origin finish declaration
        witness) := by
  apply exactInput_of_shape witness
      (LocationFragment.ofFieldDecl declaration)
  · unfold InputFragmentEquals
    exact (EbnfValue.locationFragment_transport _ _).trans
      ((EbnfValue.locationFragment_choice _ _).trans
        (EbnfValue.locationFragment_ruleAtom _ _))
  · change LocationFragment.located witness.span
      [LocationFragment.ofFieldDecl declaration] = _
    rfl
  · simp

theorem contractMemberFunction_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens) (declaration : FunctionDecl)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.contractMemberFunction origin finish declaration
        witness) := by
  apply exactInput_of_shape witness
      (LocationFragment.ofFunctionDecl declaration)
  · unfold InputFragmentEquals
    exact (EbnfValue.locationFragment_transport _ _).trans
      ((EbnfValue.locationFragment_choice _ _).trans
        (EbnfValue.locationFragment_ruleAtom _ _))
  · change LocationFragment.located witness.span
      [LocationFragment.ofFunctionDecl declaration] = _
    rfl
  · simp

theorem contractMemberFallback_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens) (declaration : FallbackDecl)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.contractMemberFallback origin finish declaration
        witness) := by
  apply exactInput_of_shape witness
      (LocationFragment.ofFallbackDecl declaration)
  · unfold InputFragmentEquals
    exact (EbnfValue.locationFragment_transport _ _).trans
      ((EbnfValue.locationFragment_choice _ _).trans
        (EbnfValue.locationFragment_ruleAtom _ _))
  · change LocationFragment.located witness.span
      [LocationFragment.ofFallbackDecl declaration] = _
    rfl
  · simp

theorem contractMemberConstructor_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (declaration : ContractConstructorDecl)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.contractMemberConstructor origin finish declaration
        witness) := by
  apply exactInput_of_shape witness
      (LocationFragment.ofContractConstructorDecl declaration)
  · unfold InputFragmentEquals
    exact (EbnfValue.locationFragment_transport _ _).trans
      ((EbnfValue.locationFragment_choice _ _).trans
        (EbnfValue.locationFragment_ruleAtom _ _))
  · change LocationFragment.located witness.span
      [LocationFragment.ofContractConstructorDecl declaration] = _
    rfl
  · simp

theorem localExportEntryItem_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens) (item : ExportItem)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.localExportEntryItem origin finish item witness) := by
  apply exactInput_of_shape witness (LocationFragment.ofExportItem item)
  · unfold InputFragmentEquals
    exact (EbnfValue.locationFragment_transport _ _).trans
      ((EbnfValue.locationFragment_choice _ _).trans
        (EbnfValue.locationFragment_ruleAtom _ _))
  · change LocationFragment.located witness.span
      [LocationFragment.ofExportItem item] = _
    rfl
  · simp

theorem remoteExportEntryItem_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens) (item : ExportItem)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.remoteExportEntryItem origin finish item witness) := by
  apply exactInput_of_shape witness (LocationFragment.ofExportItem item)
  · unfold InputFragmentEquals
    exact (EbnfValue.locationFragment_transport _ _).trans
      ((EbnfValue.locationFragment_choice _ _).trans
        (EbnfValue.locationFragment_ruleAtom _ _))
  · change LocationFragment.located witness.span
      [LocationFragment.ofExportItem item] = _
    rfl
  · simp

theorem blockStatement_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens) (body : Body)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.blockStatement origin finish body witness) := by
  apply exactInput_of_shape witness (LocationFragment.ofBody body)
  · unfold InputFragmentEquals
    exact EbnfValue.locationFragment_ruleAtom _ _
  · change LocationFragment.located witness.span
      [LocationFragment.ofBody body] = _
    rfl
  · simpa using LocationFragment.ofBody_roots_ne_nil body

theorem forInitItemLet_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens) (binding : LetBinding)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.forInitItemLet origin finish binding witness) := by
  apply exactInput_of_shape witness (LocationFragment.ofLetBinding binding)
  · unfold InputFragmentEquals
    exact (EbnfValue.locationFragment_choice _ _).trans
      (EbnfValue.locationFragment_ruleAtom _ _)
  · change LocationFragment.located witness.span
      [LocationFragment.ofLetBinding binding] = _
    rfl
  · simp

theorem forInitItemExpression_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens) (expression : Expression)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.forInitItemExpression origin finish expression
        witness) := by
  apply exactInput_of_shape witness
      (LocationFragment.ofExpression expression)
  · unfold InputFragmentEquals
    exact (EbnfValue.locationFragment_choice _ _).trans
      (EbnfValue.locationFragment_ruleAtom _ _)
  · change LocationFragment.located witness.span
      [LocationFragment.ofExpression expression] = _
    rfl
  · simp

theorem forPostItemExpression_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens) (expression : Expression)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.forPostItemExpression origin finish expression
        witness) := by
  apply exactInput_of_shape witness
      (LocationFragment.ofExpression expression)
  · unfold InputFragmentEquals
    exact (EbnfValue.locationFragment_choice _ _).trans
      (EbnfValue.locationFragment_ruleAtom _ _)
  · change LocationFragment.located witness.span
      [LocationFragment.ofExpression expression] = _
    rfl
  · simp

theorem expressionStatementTerminal_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens) (expression : Expression)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.expressionStatementTerminal origin finish expression
        witness) := by
  apply exactInput_of_shape witness
      (LocationFragment.ofExpression expression)
  · unfold InputFragmentEquals
    exact (EbnfValue.locationFragment_choice _ _).trans
      (EbnfValue.locationFragment_ruleAtom _ _)
  · rw [RuleLocationView.ofRuleValue,
      LocationFragment.ofStatement_mk]
    simp [sourceLoc, LocationFragment.ofStatementPayload,
      LocationFragment.ofOption]
  · simp

theorem patternLiteral_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens) (literal : Literal)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.patternLiteral origin finish literal witness) := by
  apply exactInput_of_shape witness (LocationFragment.ofLiteral literal)
  · unfold InputFragmentEquals
    exact (EbnfValue.locationFragment_choice _ _).trans
      (EbnfValue.locationFragment_ruleAtom _ _)
  · change LocationFragment.located witness.span
      [LocationFragment.ofLiteral literal] = _
    rfl
  · simp

theorem atomLiteral_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens) (literal : Literal)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.atomLiteral origin finish literal witness) := by
  apply exactInput_of_shape witness (LocationFragment.ofLiteral literal)
  · unfold InputFragmentEquals
    exact (EbnfValue.locationFragment_choice _ _).trans
      (EbnfValue.locationFragment_ruleAtom _ _)
  · change LocationFragment.located witness.span
      [LocationFragment.ofLiteral literal] = _
    rfl
  · simp

theorem importEntryWildcard_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (star : MatchedTerminal file tokens (.symbol .star))
    (starMarker : RuleReduction.MarkerProjects file tokens star .wildcard)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.importEntryWildcard origin finish star starMarker
        witness) := by
  apply exactInput_of_shape witness (LocationFragment.leaf star.span)
  · unfold InputFragmentEquals
    calc
      _ = star.locationFragment :=
        (EbnfValue.locationFragment_transport _ _).trans
          ((EbnfValue.locationFragment_choice _ _).trans
            (EbnfValue.locationFragment_terminalAtom _ _))
      _ = LocationFragment.leaf star.span := by
        rw [MatchedTerminal.locationFragment]
        simp
        exact (LocationFragment.leaf_eq_raw star.span).symm
  · change LocationFragment.located witness.span
      [LocationFragment.leaf star.span] = _
    rfl
  · simp [LocationFragment.leaf]

theorem localExportEntryWildcard_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (star : MatchedTerminal file tokens (.symbol .star))
    (starMarker : RuleReduction.MarkerProjects file tokens star .wildcard)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.localExportEntryWildcard origin finish star starMarker
        witness) := by
  apply exactInput_of_shape witness (LocationFragment.leaf star.span)
  · unfold InputFragmentEquals
    calc
      _ = star.locationFragment :=
        (EbnfValue.locationFragment_transport _ _).trans
          ((EbnfValue.locationFragment_choice _ _).trans
            (EbnfValue.locationFragment_terminalAtom _ _))
      _ = LocationFragment.leaf star.span := by
        rw [MatchedTerminal.locationFragment]
        simp
        exact (LocationFragment.leaf_eq_raw star.span).symm
  · change LocationFragment.located witness.span
      [LocationFragment.leaf star.span] = _
    rfl
  · simp [LocationFragment.leaf]

theorem remoteExportEntryWildcard_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (star : MatchedTerminal file tokens (.symbol .star))
    (starMarker : RuleReduction.MarkerProjects file tokens star .wildcard)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.remoteExportEntryWildcard origin finish star starMarker
        witness) := by
  apply exactInput_of_shape witness (LocationFragment.leaf star.span)
  · unfold InputFragmentEquals
    calc
      _ = star.locationFragment :=
        (EbnfValue.locationFragment_transport _ _).trans
          ((EbnfValue.locationFragment_choice _ _).trans
            (EbnfValue.locationFragment_terminalAtom _ _))
      _ = LocationFragment.leaf star.span := by
        rw [MatchedTerminal.locationFragment]
        simp
        exact (LocationFragment.leaf_eq_raw star.span).symm
  · change LocationFragment.located witness.span
      [LocationFragment.leaf star.span] = _
    rfl
  · simp [LocationFragment.leaf]

theorem forallBinderBare_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (name : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier)
    (nameProjects : IdentifierProjects name.matched name.spelling name.parsed)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.forallBinderBare origin finish name nameProjects
        witness) := by
  apply exactInput_of_shape witness
      (LocationFragment.leaf name.matched.span)
  · unfold InputFragmentEquals
    calc
      _ = name.matched.locationFragment :=
        (EbnfValue.locationFragment_transport _ _).trans
          ((EbnfValue.locationFragment_choice _ _).trans
            (EbnfValue.locationFragment_terminalAtom _ _))
      _ = LocationFragment.leaf name.matched.span := by
        rw [MatchedTerminal.locationFragment]
        simp
        exact (LocationFragment.leaf_eq_raw name.matched.span).symm
  · change LocationFragment.located witness.span
      [LocationFragment.leaf name.matched.span] = _
    rfl
  · simp [LocationFragment.leaf]

theorem patternWildcard_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (underscore : MatchedTerminal file tokens (.symbol .underscore))
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.patternWildcard origin finish underscore witness) := by
  apply exactInput_of_shape witness
      (LocationFragment.leaf underscore.span)
  · unfold InputFragmentEquals
    calc
      _ = underscore.locationFragment :=
        (EbnfValue.locationFragment_choice _ _).trans
          (EbnfValue.locationFragment_terminalAtom _ _)
      _ = LocationFragment.leaf underscore.span := by
        rw [MatchedTerminal.locationFragment]
        simp
        exact (LocationFragment.leaf_eq_raw underscore.span).symm
  · simp [RuleLocationView.ofRuleValue, sourceLoc,
      LocationFragment.ofPatternPayload, RuleReduction.marker,
      RuleReduction.terminalLoc]
  · simp [LocationFragment.leaf]

theorem atomName_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (name : MatchedTerminal file tokens (.category .identifier))
    (spelling : String) (parsed : Identifier)
    (projects : IdentifierProjects name spelling parsed)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.atomName origin finish name spelling parsed projects
        witness) := by
  apply exactInput_of_shape witness (LocationFragment.leaf name.span)
  · unfold InputFragmentEquals
    calc
      _ = name.locationFragment :=
        (EbnfValue.locationFragment_choice _ _).trans
          (EbnfValue.locationFragment_terminalAtom _ _)
      _ = LocationFragment.leaf name.span := by
        rw [MatchedTerminal.locationFragment]
        simp
        exact (LocationFragment.leaf_eq_raw name.span).symm
  · simp [RuleLocationView.ofRuleValue, sourceLoc,
      LocationFragment.ofExpressionPayload, RuleReduction.terminalLoc]
    congr 2
  · simp [LocationFragment.leaf]

theorem importEntryNamed_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (name : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier)
    (nameProjects : IdentifierProjects name.matched name.spelling name.parsed)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.importEntryNamed origin finish name nameProjects
        witness) := by
  apply exactInput_of_shape witness
      (LocationFragment.leaf name.matched.span)
  · unfold InputFragmentEquals
    refine (EbnfValue.locationFragment_transport _ _).trans ?_
    refine (EbnfValue.locationFragment_choice _ _).trans ?_
    refine (EbnfValue.locationFragment_sequence _ _).trans ?_
    apply LocationFragment.eq_of_fields <;>
      simp [MatchedTerminal.locationFragment, LocationFragment.leaf]
  · change LocationFragment.located witness.span
      [LocationFragment.ofIdentifier
        (RuleReduction.terminalLoc name.matched name.parsed)] = _
    congr 2
  · simp [LocationFragment.leaf]

theorem dataConstructorWithoutArguments_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (name : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier)
    (nameProjects : IdentifierProjects name.matched name.spelling name.parsed)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.dataConstructorWithoutArguments origin finish name
        nameProjects witness) := by
  apply exactInput_of_shape witness
      (LocationFragment.leaf name.matched.span)
  · unfold InputFragmentEquals
    refine (EbnfValue.locationFragment_transport _ _).trans ?_
    refine (EbnfValue.locationFragment_sequence _ _).trans ?_
    apply LocationFragment.eq_of_fields <;>
      simp [MatchedTerminal.locationFragment, LocationFragment.leaf]
  · change LocationFragment.located witness.span
      [LocationFragment.ofIdentifier
        (RuleReduction.terminalLoc name.matched name.parsed)] = _
    congr 2
  · simp [LocationFragment.leaf]

theorem typeAtomNamedWithoutArguments_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens) (name : QualifiedName)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.typeAtomNamedWithoutArguments origin finish name
        witness) := by
  apply exactInput_of_shape witness
      (LocationFragment.ofQualifiedName name)
  · unfold InputFragmentEquals
    refine (EbnfValue.locationFragment_transport _ _).trans ?_
    refine (EbnfValue.locationFragment_choice _ _).trans ?_
    refine (EbnfValue.locationFragment_sequence _ _).trans ?_
    apply LocationFragment.eq_of_fields <;>
      simp [RuleLocationView.ofRuleValue]
  · simp [RuleLocationView.ofRuleValue, sourceLoc,
      LocationFragment.ofTypeExprPayload,
      LocationFragment.ofTypeExprArguments]
  · simp

theorem patternNamedWithoutArguments_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens) (name : QualifiedName)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.patternNamedWithoutArguments origin finish name
        witness) := by
  apply exactInput_of_shape witness
      (LocationFragment.ofQualifiedName name)
  · unfold InputFragmentEquals
    refine (EbnfValue.locationFragment_choice _ _).trans ?_
    refine (EbnfValue.locationFragment_sequence _ _).trans ?_
    apply LocationFragment.eq_of_fields <;>
      simp [RuleLocationView.ofRuleValue]
  · simp [RuleLocationView.ofRuleValue, sourceLoc,
      LocationFragment.ofPatternPayload,
      LocationFragment.ofPatternArguments]
  · simp

theorem typeComptime_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (comptimeToken : MatchedTerminal file tokens
      (.contextualKeyword .comptimeKw))
    (inner : TypeExpr)
    (comptimeProjects : RuleReduction.MarkerProjects file tokens
      comptimeToken .comptimeModifier)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.typeComptime origin finish comptimeToken inner
        comptimeProjects witness) := by
  let core := LocationFragment.merge
    [LocationFragment.raw comptimeToken.span,
      LocationFragment.ofTypeExpr inner]
  apply exactInput_of_shape witness core
  · unfold InputFragmentEquals
    refine (EbnfValue.locationFragment_transport _ _).trans ?_
    refine (EbnfValue.locationFragment_choice _ _).trans ?_
    refine (EbnfValue.locationFragment_sequence _ _).trans ?_
    apply LocationFragment.eq_of_fields <;>
      simp [core, MatchedTerminal.locationFragment,
        RuleLocationView.ofRuleValue]
  · simp [core, RuleLocationView.ofRuleValue, sourceLoc,
      LocationFragment.ofTypeExprPayload, RuleReduction.marker,
      RuleReduction.terminalLoc, LocationFragment.leaf]
  · simp [core, LocationFragment.raw]

theorem typeAtomProxy_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (atToken : MatchedTerminal file tokens (.symbol .at))
    (inner : TypeExpr)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.typeAtomProxy origin finish atToken inner witness) := by
  let core := LocationFragment.merge
    [LocationFragment.raw atToken.span, LocationFragment.ofTypeExpr inner]
  apply exactInput_of_shape witness core
  · unfold InputFragmentEquals
    refine (EbnfValue.locationFragment_transport _ _).trans ?_
    refine (EbnfValue.locationFragment_choice _ _).trans ?_
    refine (EbnfValue.locationFragment_sequence _ _).trans ?_
    apply LocationFragment.eq_of_fields <;>
      simp [core, MatchedTerminal.locationFragment,
        RuleLocationView.ofRuleValue]
  · simp [core, RuleLocationView.ofRuleValue, sourceLoc,
      LocationFragment.ofTypeExprPayload, RuleReduction.terminalLoc,
      LocationFragment.leaf]
  · simp [core, LocationFragment.raw]

theorem patternComptime_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (comptime : MatchedTerminal file tokens
      (.contextualKeyword .comptimeKw))
    (expression : Expression)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.patternComptime origin finish comptime expression
        witness) := by
  let core := LocationFragment.merge
    [LocationFragment.raw comptime.span,
      LocationFragment.ofExpression expression]
  apply exactInput_of_shape witness core
  · unfold InputFragmentEquals
    refine (EbnfValue.locationFragment_choice _ _).trans ?_
    refine (EbnfValue.locationFragment_sequence _ _).trans ?_
    apply LocationFragment.eq_of_fields <;>
      simp [core, MatchedTerminal.locationFragment,
        RuleLocationView.ofRuleValue]
  · simp [core, RuleLocationView.ofRuleValue, sourceLoc,
      LocationFragment.ofPatternPayload, RuleReduction.marker,
      RuleReduction.terminalLoc, LocationFragment.leaf]
  · simp [core, LocationFragment.raw]

theorem prefixLogicalNot_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (bang : MatchedTerminal file tokens (.symbol .bang))
    (operand : Expression)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.prefixLogicalNot origin finish bang operand witness) := by
  let core := LocationFragment.merge
    [LocationFragment.raw bang.span,
      LocationFragment.ofExpression operand]
  apply exactInput_of_shape witness core
  · unfold InputFragmentEquals
    refine (EbnfValue.locationFragment_choice _ _).trans ?_
    refine (EbnfValue.locationFragment_sequence _ _).trans ?_
    apply LocationFragment.eq_of_fields <;>
      simp [core, MatchedTerminal.locationFragment,
        RuleLocationView.ofRuleValue]
  · simp [core, RuleLocationView.ofRuleValue, sourceLoc,
      LocationFragment.ofExpressionPayload, RuleReduction.prefixOperator,
      RuleReduction.terminalLoc, LocationFragment.leaf]
  · simp [core, LocationFragment.raw]

theorem atomProxy_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (atTerminal : MatchedTerminal file tokens (.symbol .at))
    (typeValue : TypeExpr)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.atomProxy origin finish atTerminal typeValue witness) := by
  let core := LocationFragment.merge
    [LocationFragment.raw atTerminal.span,
      LocationFragment.ofTypeExpr typeValue]
  apply exactInput_of_shape witness core
  · unfold InputFragmentEquals
    refine (EbnfValue.locationFragment_choice _ _).trans ?_
    refine (EbnfValue.locationFragment_sequence _ _).trans ?_
    apply LocationFragment.eq_of_fields <;>
      simp [core, MatchedTerminal.locationFragment,
        RuleLocationView.ofRuleValue]
  · simp [core, RuleLocationView.ofRuleValue, sourceLoc,
      LocationFragment.ofExpressionPayload, RuleReduction.terminalLoc,
      LocationFragment.leaf]
  · simp [core, LocationFragment.raw]

theorem moduleRefRelativeLibraryEmpty_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (first : RuleReduction.SpelledTerminalData file tokens
      (.category .pathComponent) PathSegment)
    (firstProjects : PathSegmentProjects first.matched
      first.spelling first.parsed)
    (libraryMarker : RuleReduction.MarkerProjects file tokens
      first.matched .libraryRoot)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.moduleRefRelativeLibraryEmpty origin finish first
        firstProjects libraryMarker witness) := by
  apply exactInput_of_shape witness
      (LocationFragment.leaf first.matched.span)
  · unfold InputFragmentEquals
    refine (EbnfValue.locationFragment_transport _ _).trans ?_
    refine (EbnfValue.locationFragment_choice _ _).trans ?_
    refine (EbnfValue.locationFragment_sequence _ _).trans ?_
    rw [EbnfValues.locationFragment_cons]
    rw [EbnfValues.locationFragment_cons]
    rw [EbnfValues.locationFragment_nil]
    rw [EbnfValue.locationFragment_star]
    apply LocationFragment.eq_of_fields <;>
      simp [MatchedTerminal.locationFragment, LocationFragment.leaf]
  · change LocationFragment.located witness.span
      [LocationFragment.leaf first.matched.span] = _
    rfl
  · simp [LocationFragment.leaf]

theorem genericPrefixBare_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens) (forallClause : ForallClause)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.genericPrefixBare origin finish forallClause
        witness) := by
  apply exactInput_of_shape witness
      (LocationFragment.ofForallClause forallClause)
  · unfold InputFragmentEquals
    refine (EbnfValue.locationFragment_transport _ _).trans ?_
    refine (EbnfValue.locationFragment_sequence _ _).trans ?_
    apply LocationFragment.eq_of_fields <;>
      simp [RuleLocationView.ofRuleValue]
  · change LocationFragment.located witness.span
      [LocationFragment.ofForallClause forallClause] = _
    rfl
  · simp

theorem functionDecl_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens) (signature : FunctionSignature)
    (body : Body)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.functionDecl origin finish signature body witness) := by
  let core := LocationFragment.merge
    [LocationFragment.ofFunctionSignature signature,
      LocationFragment.ofBody body]
  apply exactInput_of_shape witness core
  · unfold InputFragmentEquals
    refine (EbnfValue.locationFragment_transport _ _).trans ?_
    refine (EbnfValue.locationFragment_sequence _ _).trans ?_
    apply LocationFragment.eq_of_fields <;>
      simp [core, RuleLocationView.ofRuleValue]
  · change LocationFragment.located witness.span
      [LocationFragment.ofFunctionSignature signature,
        LocationFragment.ofBody body] =
        LocationFragment.located witness.span [core]
    exact (LocationFragment.located_merge _ _).symm
  · simp [core]

theorem classMethod_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens) (signature : FunctionSignature)
    (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.classMethod origin finish signature semicolon
        witness) := by
  let core := LocationFragment.merge
    [LocationFragment.ofFunctionSignature signature,
      LocationFragment.raw semicolon.span]
  apply exactInput_of_shape witness core
  · unfold InputFragmentEquals
    refine (EbnfValue.locationFragment_transport _ _).trans ?_
    refine (EbnfValue.locationFragment_sequence _ _).trans ?_
    apply LocationFragment.eq_of_fields <;>
      simp [core, RuleLocationView.ofRuleValue,
        MatchedTerminal.locationFragment]
  · change LocationFragment.located witness.span
      [LocationFragment.ofFunctionSignature signature,
        LocationFragment.raw semicolon.span] =
        LocationFragment.located witness.span [core]
    exact (LocationFragment.located_merge _ _).symm
  · simp [core, LocationFragment.raw]

theorem expressionStatementTerminated_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens) (expression : Expression)
    (semicolon : MatchedTerminal file tokens (.symbol .semicolon))
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.expressionStatementTerminated origin finish expression
        semicolon witness) := by
  let core := LocationFragment.merge
    [LocationFragment.ofExpression expression,
      LocationFragment.raw semicolon.span]
  apply exactInput_of_shape witness core
  · unfold InputFragmentEquals
    refine (EbnfValue.locationFragment_choice _ _).trans ?_
    refine (EbnfValue.locationFragment_sequence _ _).trans ?_
    apply LocationFragment.eq_of_fields <;>
      simp [core, RuleLocationView.ofRuleValue,
        MatchedTerminal.locationFragment]
  · rw [RuleLocationView.ofRuleValue,
      LocationFragment.ofStatement_mk]
    simp [core, sourceLoc, LocationFragment.ofStatementPayload,
      LocationFragment.ofOption]
  · simp [core]

theorem patternDotConstructorWithoutArguments_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (dot : MatchedTerminal file tokens (.symbol .dot))
    (name : MatchedTerminal file tokens (.category .identifier))
    (spelling : String) (parsed : Identifier)
    (projects : IdentifierProjects name spelling parsed)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.patternDotConstructorWithoutArguments origin finish dot
        name spelling parsed projects witness) := by
  let core := LocationFragment.merge
    [LocationFragment.raw dot.span, LocationFragment.raw name.span]
  apply exactInput_of_shape witness core
  · unfold InputFragmentEquals
    refine (EbnfValue.locationFragment_choice _ _).trans ?_
    refine (EbnfValue.locationFragment_sequence _ _).trans ?_
    apply LocationFragment.eq_of_fields <;>
      simp [core, MatchedTerminal.locationFragment]
  · have nameFragment :
        LocationFragment.ofIdentifier
            (RuleReduction.terminalLoc name parsed) =
          LocationFragment.raw name.span :=
      LocationFragment.leaf_eq_raw name.span
    simp only [RuleLocationView.ofRuleValue, sourceLoc,
      LocationFragment.ofPattern_mk,
      LocationFragment.ofPatternPayload,
      LocationFragment.ofPatternArguments]
    rw [nameFragment]
    apply LocationFragment.eq_of_fields <;>
      simp [core, LocationFragment.leaf, RuleReduction.terminalLoc]
  · simp [core]

theorem atomDotConstructorWithoutArguments_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (dot : MatchedTerminal file tokens (.symbol .dot))
    (name : MatchedTerminal file tokens (.category .identifier))
    (spelling : String) (parsed : Identifier)
    (projects : IdentifierProjects name spelling parsed)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.atomDotConstructorWithoutArguments origin finish dot name
        spelling parsed projects witness) := by
  let core := LocationFragment.merge
    [LocationFragment.raw dot.span, LocationFragment.raw name.span]
  apply exactInput_of_shape witness core
  · unfold InputFragmentEquals
    refine (EbnfValue.locationFragment_choice _ _).trans ?_
    refine (EbnfValue.locationFragment_sequence _ _).trans ?_
    apply LocationFragment.eq_of_fields <;>
      simp [core, MatchedTerminal.locationFragment]
  · have nameFragment :
        LocationFragment.ofIdentifier
            (RuleReduction.terminalLoc name parsed) =
          LocationFragment.raw name.span :=
      LocationFragment.leaf_eq_raw name.span
    simp only [RuleLocationView.ofRuleValue, sourceLoc,
      LocationFragment.ofExpression_mk,
      LocationFragment.ofExpressionPayload,
      LocationFragment.ofExpressionListOption]
    rw [nameFragment]
    apply LocationFragment.eq_of_fields <;>
      simp [core, LocationFragment.leaf, RuleReduction.terminalLoc]
  · simp [core]

theorem exportItem_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (name : RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier)
    (selection : Option ConstructorSelection)
    (nameProjects : IdentifierProjects name.matched name.spelling name.parsed)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.exportItem origin finish name selection nameProjects
        witness) := by
  let retainedName := RuleReduction.terminalLoc name.matched name.parsed
  let core := LocationFragment.merge
    [LocationFragment.raw name.matched.span,
      LocationFragment.ofOption LocationFragment.ofConstructorSelection
        selection]
  apply exactInput_of_shape witness core
  · unfold InputFragmentEquals
    refine (EbnfValue.locationFragment_transport _ _).trans ?_
    refine (EbnfValue.locationFragment_sequence _ _).trans ?_
    rw [EbnfValues.locationFragment_cons]
    rw [EbnfValues.locationFragment_cons]
    rw [EbnfValues.locationFragment_nil]
    rw [EbnfValue.locationFragment_terminalAtom]
    cases selection with
    | none =>
        simp only [Option.map]
        rw [EbnfValue.locationFragment_optional_none]
        apply LocationFragment.eq_of_fields <;>
          simp [core, LocationFragment.ofOption,
            MatchedTerminal.locationFragment]
    | some selected =>
        simp only [Option.map]
        rw [EbnfValue.locationFragment_optional_some]
        rw [EbnfValue.locationFragment_ruleAtom]
        apply LocationFragment.eq_of_fields <;>
          simp [core, LocationFragment.ofOption,
            MatchedTerminal.locationFragment, RuleLocationView.ofRuleValue]
  · change LocationFragment.located witness.span
      [LocationFragment.ofIdentifier retainedName,
        LocationFragment.ofOption LocationFragment.ofConstructorSelection
          selection] = LocationFragment.located witness.span [core]
    have nameFragment :
        LocationFragment.ofIdentifier retainedName =
          LocationFragment.raw name.matched.span :=
      LocationFragment.leaf_eq_raw name.matched.span
    rw [nameFragment]
    exact (LocationFragment.located_merge _ _).symm
  · simp [core]

theorem hidingClause_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (hidingKw : MatchedTerminal file tokens (.hardKeyword .hidingKw))
    (openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
    (names : List (RuleReduction.SpelledTerminalData file tokens
      (.category .identifier) Identifier))
    (closeBrace : MatchedTerminal file tokens (.symbol .rightBrace))
    (nameProjects : ∀ name, name ∈ names →
      IdentifierProjects name.matched name.spelling name.parsed)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.hidingClause origin finish hidingKw openBrace names
        closeBrace nameProjects witness) := by
  let retained : List IdentifierOccurrence := names.map fun name =>
    RuleReduction.terminalLoc name.matched name.parsed
  let core := LocationFragment.merge
    (names.map fun name => name.matched.locationFragment)
  have retainedFragments :
      retained.map LocationFragment.ofIdentifier =
        names.map fun name => name.matched.locationFragment := by
    dsimp [retained]
    rw [List.map_map]
    apply List.map_congr_left
    intro name member
    change LocationFragment.located name.matched.span [] =
      name.matched.locationFragment
    simp [MatchedTerminal.locationFragment]
  apply WrappedLocation.projectedInput witness core
  · change LocationFragment.ofHidingClause
      ⟨witness.span, ⟨retained⟩⟩ =
        LocationFragment.located witness.span [core]
    rw [LocationFragment.ofHidingClause_mk, retainedFragments]
  · apply LocationFragment.IsSubfragmentOf.merge_map
    intro name member
    apply EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
    apply EbnfValue.ContainsLocationFragment.transport (by rfl)
    apply EbnfValue.ContainsLocationFragment.sequence
    apply EbnfValues.ContainsLocationFragment.tail
    apply EbnfValues.ContainsLocationFragment.tail
    apply EbnfValues.ContainsLocationFragment.head
    apply EbnfValue.ContainsLocationFragment.list0
    · rw [List.mem_map]
      exact ⟨name, member, rfl⟩
    · exact EbnfValue.ContainsLocationFragment.terminal _ _
  · simp [MatchedTerminal.locationFragment]

theorem typeAtomEmptyTuple_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (openParen : MatchedTerminal file tokens (.symbol .leftParen))
    (closeParen : MatchedTerminal file tokens (.symbol .rightParen))
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.typeAtomEmptyTuple origin finish openParen closeParen
        witness) := by
  apply WrappedLocation.projectedInput witness LocationFragment.empty
  · simp [RuleLocationView.ofRuleValue, sourceLoc,
      LocationFragment.ofTypeExprPayload,
      LocationFragment.ofTypeExprList]
  · exact LocationFragment.IsSubfragmentOf.empty _
  · simp [MatchedTerminal.locationFragment]

theorem patternEmptyTuple_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (openParen : MatchedTerminal file tokens (.symbol .leftParen))
    (closeParen : MatchedTerminal file tokens (.symbol .rightParen))
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.patternEmptyTuple origin finish openParen closeParen
        witness) := by
  apply WrappedLocation.projectedInput witness LocationFragment.empty
  · simp [RuleLocationView.ofRuleValue, sourceLoc,
      LocationFragment.ofPatternPayload,
      LocationFragment.ofPatternList]
  · exact LocationFragment.IsSubfragmentOf.empty _
  · apply LocationFragment.IsSubfragmentOf.roots_ne_nil
      (inner := openParen.locationFragment)
    · apply
        EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.choice ⟨5, by decide⟩
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.terminal _ _
    · simp [MatchedTerminal.locationFragment]

theorem atomEmptyTuple_case
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (openParen : MatchedTerminal file tokens (.symbol .leftParen))
    (closeParen : MatchedTerminal file tokens (.symbol .rightParen))
    (witness : ConsumedSpanWitness file tokens origin finish) :
    WrappedLocation
      (RuleReduction.atomEmptyTuple origin finish openParen closeParen
        witness) := by
  apply WrappedLocation.projectedInput witness LocationFragment.empty
  · simp [RuleLocationView.ofRuleValue, sourceLoc,
      LocationFragment.ofExpressionPayload,
      LocationFragment.ofExpressionList]
  · exact LocationFragment.IsSubfragmentOf.empty _
  · apply LocationFragment.IsSubfragmentOf.roots_ne_nil
      (inner := openParen.locationFragment)
    · apply
        EbnfValue.ContainsLocationFragment.locationFragment_isSubfragment
      apply EbnfValue.ContainsLocationFragment.choice ⟨5, by decide⟩
      apply EbnfValue.ContainsLocationFragment.sequence
      apply EbnfValues.ContainsLocationFragment.head
      exact EbnfValue.ContainsLocationFragment.terminal _ _
    · simp [MatchedTerminal.locationFragment]

end RuleReduction.WrappedLocation

end Solcore.Surface.Multi
