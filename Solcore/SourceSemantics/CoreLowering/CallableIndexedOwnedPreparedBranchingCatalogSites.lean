import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBranchingTree
import Solcore.SourceSemantics.CoreLowering.GenericImperativeForMatchEmbedding

/-! Bare plain assignments have no reachable place or operand diagnostic.
The original fragment shape supplies catalog sites for the same compiler tree. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedBranchingCatalogSites
open Core Frontend SourceInference SourceCoreCompatibleDataPlaces CompatiblePayload
open CallableIndexedOwnedPreparedStagedBranchingTree

private theorem empty_steps
    {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {context : SourceSemantics.Context} {certificate : GenericExpressionMeaning.Certificate}
    {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context} {definitions : DataEnvironment}
    {place : PlaceResolution} {prepared : SourceCoreCompatibleDataPlaces.Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {leaf : TypeSystem.Ty}
    (shape : GenericAssignmentStatements.Shape values source context certificate scope administrative
      definitions place prepared codes leaf) (bare : place.projections = []) : prepared.steps = [] := by
  cases shape with
  | bare _ layout => exact layout.steps
  | projected layout _ =>
    have length := CompatiblePlaceCompilerCertificates.PreparedPath.steps_length layout.path
    rw [bare, List.length_nil] at length
    exact False.elim (layout.nonempty (List.eq_nil_of_length_eq_zero length))

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {definitions : DataEnvironment} {administrative : Core.Context}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {position : GenericImperativeMatch.Position} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}

theorem sites
    (tree : GenericImperativeMatch.Tree layouts owner active frame globals onError values source
      expressionSyntax certificates definitions administrative context scope position expected type code)
    {mode : Bool} {statements : List StatementId} (atStatements : position = .statements mode statements)
    (shape : Shape source mode statements) : tree.CatalogSites .reachable registry faults := by
  induction tree generalizing mode statements with
  | body syntaxTree body => exact .body (syntaxTree := syntaxTree) (body := body)
  | uninitialized found form mono extended ordinary projected allocation annotation same remaining ih =>
    cases atStatements
    exact .uninitialized (found := found) (form := form) (monomorphic := mono) (extended := extended)
      (ordinary := ordinary) (projected := projected) (allocation := allocation) (annotation := annotation)
      (same := same) (remaining := remaining) (ih rfl (shape.tail_of_let found form))
  | initialized found form mono extended ordinary initFound sourceType initial allocation annotation same remaining ih =>
    cases atStatements
    exact .initialized (found := found) (form := form) (monomorphic := mono) (extended := extended)
      (ordinary := ordinary) (initializerFound := initFound) (sourceType := sourceType) (initial := initial)
      (allocation := allocation) (annotation := annotation) (same := same) (remaining := remaining)
      (ih rfl (shape.tail_of_let found form))
  | discard found form notTail expressionFound value remaining ih =>
    cases atStatements
    exact .discard (found := found) (form := form) (notTail := notTail)
      (expressionFound := expressionFound) (value := value) (remaining := remaining)
      (ih rfl (shape.discard_tail found form notTail).2)
  | assign found form head rest ih =>
    cases atStatements
    obtain ⟨same, bare, remaining⟩ := shape.assign_tail found form
    cases same
    apply GenericImperativeMatch.Tree.CatalogSites.assign (found := found) (form := form)
      (head := head) (remaining := rest)
    · exact ih rfl remaining
    · exact GenericAssignmentStatements.Head.ReachableErrors.bare_equal (empty_steps head.shape bare)
  | block found form _ _ _ _ | terminalBlock _ found form _ _ _ _ =>
    cases atStatements
    exact False.elim (shape.not_block found form)
  | ifThen found form conditionFound conditionType conditionTree thenTree elseTree remaining leftIH rightIH nextIH =>
    cases atStatements
    obtain ⟨left, right, next⟩ := shape.branches found form
    exact .ifThen (found := found) (form := form) (conditionFound := conditionFound)
      (conditionType := conditionType) (conditionTree := conditionTree)
      (thenTree := thenTree) (elseTree := elseTree) (remaining := remaining)
      (leftIH rfl left) (rightIH rfl right) (nextIH rfl next)
  | terminalIf unique found form conditionFound conditionType conditionTree thenTree elseTree thenStops elseStops issued leftIH rightIH =>
    cases atStatements
    obtain ⟨left, right, _next⟩ := shape.branches found form
    exact .terminalIf (unique := unique) (found := found) (form := form)
      (conditionFound := conditionFound) (conditionType := conditionType) (conditionTree := conditionTree)
      (thenTree := thenTree) (elseTree := elseTree) (thenStops := thenStops) (elseStops := elseStops)
      (issued := issued) (leftIH rfl left) (rightIH rfl right)
  | breaking found form | continuing found form =>
    cases atStatements
    have no := shape.head_allowed found
    simp only [form, allowedForm, Bool.false_eq_true] at no
  | whileLoop found form _ _ _ _ _ _ _ _ | forLoop found form _ _ _ _
  | bitNot found form _ _ _ | matchWith found form _ _ _ _ _ _ _ _ _ _ _ _ _ _
  | terminalMatch _ found form _ _ _ _ _ _ _ _ _ _ _ _ _ =>
    cases atStatements
    have no := shape.head_allowed found
    simp only [form, allowedForm, Bool.false_eq_true] at no
  | initializersDone | initializerUninitialized | initializerInitialized | initializerDiscard
  | initializerAssign | initializerBitNot => cases atStatements

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedBranchingCatalogSites
