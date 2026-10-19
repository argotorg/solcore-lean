import Solcore.SourceSemantics.CoreLowering.CellAwareSourceReadLifting
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedReadProductTreeBounds
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionProductSource

/-! This compiler fragment contains only original reads, literals and products.
Its independent Source derivation lifts structurally; every reached child heap
is passed directly and no execution relation is assumed. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareSourceReadProductLifting
open Core Frontend SourceInference Staging.Recursive.Lifting
open CallableIndexedOwnedPreparedStagedReadProductTreeBounds (Certificate)

private theorem literal_atomic {solved node type code}
    (literal : CompatibleExpressionLiterals.Literal solved node type code) :
    Staging.Recursive.AtomicForm node.form := by
  cases literal with
  | unit form _ _ _ => rw [form]; exact .unit
  | bool value form _ _ _ => rw [form]; exact .reference _ _
  | word value form _ _ _ _ => rw [form]; exact .literal _
  | resolvedWord form _ | resolvedInteger form _ => rw [form]; exact .integerLiteral _ _

private theorem literal_coercions {solved node type code}
    (literal : CompatibleExpressionLiterals.Literal solved node type code) : node.coercions = [] := by
  cases literal with
  | unit _ _ _ empty | bool _ _ _ _ empty | word _ _ _ _ empty _ => exact empty
  | resolvedWord _ metadata | resolvedInteger _ metadata => exact metadata.coercions

private theorem literal_nonlocal {solved node type code}
    (literal : CompatibleExpressionLiterals.Literal solved node type code) :
    ∀ name binder, node.form ≠ .reference name (.local binder) := by
  cases literal with
  | unit form _ _ _ | bool _ form _ _ _ | word _ form _ _ _ _
  | resolvedWord form _ | resolvedInteger form _ => intros; simp [form]

theorem exact_trace {values : SourceCoreCompatibleValues.Context}
    {program : Program} {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
    {context : SourceSemantics.Context} {readFuel : Nat} {reasonAt : ExpressionId → Word}
    {solved : List SolvedRequirement} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {lowered : SourceCoreBasic.LoweredExpr}
    (certificate : Certificate readFuel values invocation.source context solved reasonAt scope id lowered)
    (unique : NodeOccurrencesUnique invocation.source) :
    ∀ {environment before outcome after},
      Dynamic.ExpressionEvaluatesOutcome program context invocation.evidence invocation.source
        environment before id outcome after →
      Staging.Recursive.Expression program registry invocation context environment before id (embed outcome) after := by
  obtain ⟨tree, sites⟩ := certificate
  induction sites with
  | literal _ receipt =>
    intro environment before outcome after trace
    obtain ⟨node, found, literal, _⟩ := receipt
    exact Staging.Recursive.Lifting.atomic_nonlocal unique (lookupExpression?_sound found)
      (literal_atomic literal) (literal_coercions literal) (literal_nonlocal literal) trace
  | read receipt =>
    intro environment before outcome after trace
    obtain ⟨read, _, _⟩ := receipt
    exact CellAwareSourceReadLifting.read unique read.metadata.found read.form read.metadata.coercions trace
  | group metadata form innerFound sourceType child childSites ih =>
    intro environment before outcome after trace
    exact .group ⟨_, lookupExpression?_sound metadata.found, form, metadata.requirements, metadata.coercions⟩
      (ih (CompatibleExpressionProducts.group_inv metadata form unique trace))
  | pair metadata form leftFound rightFound sourceType leftTree rightTree leftSites rightSites leftIH rightIH =>
    intro environment before outcome after trace
    have occurrence : Staging.Recursive.Occurrence invocation _ (.tuple [_, _]) :=
      ⟨_, lookupExpression?_sound metadata.found, form, metadata.requirements, metadata.coercions⟩
    obtain ⟨sequence, children, packed⟩ := CompatibleExpressionProducts.pair_inv metadata form unique trace
    cases packed with
    | values pack =>
      cases children with
      | values children =>
        cases children with
        | cons first rest =>
          cases rest with
          | cons second rest =>
            cases rest
            cases pack with
            | cons tail =>
              cases tail
              exact .pair occurrence (leftIH (.value first)) (rightIH (.value second))
    | fault reason =>
      cases children with
      | fault failed =>
        cases failed with
        | head head => exact .pairLeftFault occurrence (leftIH (.fault head))
        | tail head tail =>
          cases tail with
          | head failed => exact .pairRightFault occurrence (leftIH (.value head)) (rightIH (.fault failed))
          | tail _ impossible => cases impossible

end Solcore.SourceSemantics.CoreLowering.CellAwareSourceReadProductLifting
