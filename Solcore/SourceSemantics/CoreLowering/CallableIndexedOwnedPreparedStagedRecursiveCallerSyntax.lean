import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates

/-! Supported Source grammar follows the exact finite compiler-certificate
paths. Declaration-call paths contain only evaluated arguments; their metadata
callee remains an authentic static occurrence rather than an evaluated child. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (Certificate Calls DirectCalls Syntax GeneralSyntax NoDirect)

theorem syntax_child {source : TypedSource} {id child : ExpressionId}
    {node : ExpressionNode} (tree : Syntax source id)
    (found : source.lookupExpression? id = some node)
    (edge : (.expression child : NodeId) ∈ node.form.references) : Syntax source child := by
  cases tree with
  | leaf finite =>
      cases finite with
      | literal selected atomic =>
          cases Option.some.inj (selected.symm.trans found)
          generalize formEq : node.form = actualForm at atomic
          cases atomic <;> simp [formEq, ExpressionForm.references] at edge
      | read selected form =>
          cases Option.some.inj (selected.symm.trans found)
          simp [form, ExpressionForm.references] at edge
      | @group _ _ inner selected form innerTree =>
          cases Option.some.inj (selected.symm.trans found)
          have same : child = inner := by simpa [form, ExpressionForm.references] using edge
          exact same.symm ▸ Syntax.leaf innerTree
      | @pair _ _ left right selected form first second =>
          cases Option.some.inj (selected.symm.trans found)
          have member : child = left ∨ child = right := by
            simpa [form, ExpressionForm.references] using edge
          rcases member with same | same
          · exact same.symm ▸ Syntax.leaf first
          · exact same.symm ▸ Syntax.leaf second
  | @group _ _ inner selected form innerTree =>
      cases Option.some.inj (selected.symm.trans found)
      have same : child = inner := by simpa [form, ExpressionForm.references] using edge
      exact same.symm ▸ innerTree
  | tuple selected form children =>
      cases Option.some.inj (selected.symm.trans found)
      exact children child (by simpa [form, ExpressionForm.references] using edge)
  | constructor selected form _ranges children =>
      cases Option.some.inj (selected.symm.trans found)
      exact children child (by simpa [form, ExpressionForm.references] using edge)
  | @call _ _ callee ids _ selected form calleeTree children =>
      cases Option.some.inj (selected.symm.trans found)
      have member : child = callee ∨ child ∈ ids := by
        simpa [form, ExpressionForm.references] using edge
      rcases member with same | member
      · exact same.symm ▸ calleeTree
      · exact children child member
  | @unary _ _ operator operand selected form childTree =>
      cases Option.some.inj (selected.symm.trans found)
      have same : child = operand := by simpa [form, ExpressionForm.references] using edge
      exact same.symm ▸ childTree
  | @binary _ _ left operator right selected form first second =>
      cases Option.some.inj (selected.symm.trans found)
      have member : child = left ∨ child = right := by simpa [form, ExpressionForm.references] using edge
      rcases member with same | same
      · exact same.symm ▸ first
      · exact same.symm ▸ second
  | @conditional _ _ test yes no selected form testTree yesTree noTree =>
      cases Option.some.inj (selected.symm.trans found)
      have member : child = test ∨ child = yes ∨ child = no := by simpa [form, ExpressionForm.references] using edge
      rcases member with same | same | same
      · exact same.symm ▸ testTree
      · exact same.symm ▸ yesTree
      · exact same.symm ▸ noTree

private theorem literal_syntax {solved : List SolvedRequirement}
    {source : TypedSource} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : CompatibleExpressionLiterals.Certificate solved source id lowered) :
    CompatibleExpressionProducts.Syntax source id := by
  rcases lowered with ⟨type, expression⟩
  obtain ⟨node, found, literal⟩ := receipt
  refine .literal found ?_
  cases literal with
  | unit form _type _requirements _coercions =>
    rw [form]
    exact .unit
  | bool value form _type _requirements _coercions =>
    rw [form]
    exact .bool _ value
  | word value form _type _requirements _coercions _meaning =>
    rw [form]
    exact .word _
  | resolvedWord form _metadata | resolvedInteger form _metadata =>
    rw [form]
    exact .integer _ _

private theorem product_syntax {fuel : Nat} {values : SourceCoreCompatibleValues.Context}
    {source : TypedSource} {context : SourceSemantics.Context} {solved : List SolvedRequirement}
    {reasonAt : ExpressionId → Word} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : CompatibleExpressionProducts.Tree fuel values source context solved reasonAt scope id lowered) :
    CompatibleExpressionProducts.Syntax source id := by
  induction tree with
  | literal receipt => exact literal_syntax receipt
  | read receipt =>
    obtain ⟨certificate, _type, _binding⟩ := receipt
    exact .read certificate.metadata.found certificate.form
  | group metadata form _found _sourceType _child ih =>
    exact .group metadata.found form ih
  | pair metadata form _leftFound _rightFound _sourceType _first _second firstIH secondIH =>
    exact .pair metadata.found form firstIH secondIH

private theorem sequence_length {source : TypedSource}
    {certificate : GenericExpressionMeaning.Certificate} {scope : SourceCoreLocalCell.Scope}
    {ids : List ExpressionId} {types : List TypeSystem.Ty}
    {codes : List SourceCoreBasic.LoweredExpr}
    (tree : DataExpressionSequence.Tree source certificate scope ids types codes) :
    ids.length = codes.length := by
  induction tree with
  | nil => rfl
  | single _found _generated => rfl
  | cons _found _generated _tail ih => exact congrArg Nat.succ ih

private theorem zip_member {α β : Type} {xs : List α} {ys : List β}
    (same : xs.length = ys.length) {x : α} (member : x ∈ xs) :
    ∃ y, (x, y) ∈ xs.zip ys := by
  induction xs generalizing ys with
  | nil => cases member
  | cons head rest ih =>
    cases ys with
    | nil => cases same
    | cons first tail =>
      have remaining : rest.length = tail.length := Nat.succ.inj same
      rcases List.mem_cons.mp member with equal | inside
      · subst x
        refine ⟨first, ?_⟩
        change (head, first) ∈ (head, first) :: rest.zip tail
        exact List.mem_cons_self
      · obtain ⟨y, paired⟩ := ih remaining inside
        refine ⟨y, ?_⟩
        change (x, y) ∈ (head, first) :: rest.zip tail
        exact List.mem_cons_of_mem _ paired

variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
  {compilation : SourceCoreFunctions.Context} {readFuel : Nat}
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {context : SourceSemantics.Context} {reasonAt : ExpressionId → Word}

/-- Every actual certificate reconstructs its supported original grammar.
The physical argument rows are retained; no occurrence set replaces them. -/
theorem certificate_syntax {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (tree : Certificate policy body compilation readFuel values source context reasonAt scope id lowered) :
    GeneralSyntax source id := by
  induction tree with
  | leaf tree =>
    obtain ⟨product, _literalSites⟩ := tree
    exact .leaf (product_syntax product)
  | group metadata form _found _sourceType _child ih =>
    exact .group metadata.found form ih
  | @tuple id node ids types codes header sequence children ih =>
    refine .tuple header.metadata.found header.form ?_
    intro child member
    obtain ⟨code, paired⟩ := zip_member (sequence_length sequence) member
    exact ih child code paired
  | @constructor id node instantiation ids tag headerWord codes header form admissible ranges count nodes sequence children ih =>
    refine .constructor header.metadata.found form ranges ?_
    intro child member
    obtain ⟨code, paired⟩ := zip_member (sequence_length sequence) member
    exact ih child code paired
  | @direct id callee ids instantiation fuel lowered types compiler calleeTyped application sequence children ih =>
    refine .direct compiler.metadata.found compiler.form compiler.monomorphic ?_
    intro child member
    obtain ⟨code, paired⟩ := zip_member (sequence_length sequence) member
    exact ih child code paired
  | @call id callee ids metadata fuel lowered types compiler sequence children ih =>
    refine .call compiler.found compiler.originalForm ?_ ?_
    · apply ih callee compiler.calleeCode
      change (callee, compiler.calleeCode) ∈ (callee, compiler.calleeCode) :: ids.zip compiler.codes
      exact List.mem_cons_self
    · intro child member
      obtain ⟨code, paired⟩ := zip_member (sequence_length sequence) member
      apply ih child code
      change (child, code) ∈ (callee, compiler.calleeCode) :: ids.zip compiler.codes
      exact List.mem_cons_of_mem _ paired
  | unary metadata form _found _input _output _profile _child ih =>
    exact .unary metadata.found form ih
  | binary metadata form _leftFound _rightFound _leftType _rightType _output _profile _first _second firstIH secondIH =>
    exact .binary metadata.found form firstIH secondIH
  | conditional metadata form _conditionFound _thenFound _elseFound _conditionType _thenType _elseType _test _yes _no testIH yesIH noIH =>
    exact .conditional metadata.found form testIH yesIH noIH

/-- Grammar at a reached call comes from its literal Calls path and certificate,
including the leading callee and ordered argument entries. -/
theorem calls_syntax {callFuel : Nat} {callScope : SourceCoreLocalCell.Scope}
    {callId callee : ExpressionId} {ids : List ExpressionId}
    {metadata : IndirectCallResolution} {lowered : SourceCoreBasic.LoweredExpr}
    {compiler : CallableIndirectCallCertificates.Receipt policy body callFuel compilation
      source callScope callId callee ids metadata reasonAt lowered}
    {rootScope : SourceCoreLocalCell.Scope} {rootId : ExpressionId}
    {rootCode : SourceCoreBasic.LoweredExpr}
    {root : Certificate policy body compilation readFuel values source context
      reasonAt rootScope rootId rootCode}
    (path : Calls compiler root) : GeneralSyntax source callId := by
  induction path with
  | here sequence children => exact certificate_syntax (.call compiler sequence children)
  | group _inside ih => exact ih
  | tuple_child _member _inside ih | constructor_child _member _inside ih
  | direct_child _member _inside ih => exact ih
  | call_child _member _inside ih => exact ih
  | unary_child _inside ih | binary_left _inside ih | binary_right _inside ih
  | conditional_condition _inside ih | conditional_then _inside ih | conditional_else _inside ih => exact ih

/-- Grammar at a reached call comes from its literal Calls path and certificate,
including the leading callee and ordered argument entries. -/
theorem direct_calls_syntax {callFuel : Nat} {callScope : SourceCoreLocalCell.Scope}
    {callId callee : ExpressionId} {ids : List ExpressionId}
    {instantiation : DeclarationInstantiation} {lowered : SourceCoreBasic.LoweredExpr}
    {compiler : CallableIndexedOwnedPreparedStagedDirectCallCertificates.Receipt policy body callFuel compilation
      values source callScope callId callee ids instantiation reasonAt lowered}
    {rootScope : SourceCoreLocalCell.Scope} {rootId : ExpressionId}
    {rootCode : SourceCoreBasic.LoweredExpr}
    {root : Certificate policy body compilation readFuel values source context
      reasonAt rootScope rootId rootCode}
    (path : DirectCalls compiler root) : GeneralSyntax source callId := by
  induction path with
  | here calleeTyped application sequence children => exact certificate_syntax (.direct compiler calleeTyped application sequence children)
  | group _inside ih => exact ih
  | tuple_child _member _inside ih | constructor_child _member _inside ih
  | direct_child _member _inside ih => exact ih
  | call_child _member _inside ih => exact ih
  | unary_child _inside ih | binary_left _inside ih | binary_right _inside ih
  | conditional_condition _inside ih | conditional_then _inside ih | conditional_else _inside ih => exact ih


/-- Declaration calls are absent from the established legacy grammar. -/
theorem syntax_not_direct {source : TypedSource} {id : ExpressionId} {node : ExpressionNode}
    {callee : ExpressionId} {ids : List ExpressionId} {instantiation : DeclarationInstantiation}
    (tree : Syntax source id) (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee ids (.declaration instantiation)) : False := by
  cases tree with
  | leaf finite =>
    cases finite with
    | literal selected atomic =>
      cases Option.some.inj (selected.symm.trans found)
      rw [form] at atomic
      cases atomic
    | read selected actual | group selected actual _ | pair selected actual _ _ =>
      cases Option.some.inj (selected.symm.trans found)
      simp [form] at actual
  | group selected actual _ | tuple selected actual _ | constructor selected actual _ _
  | call selected actual _ _ | unary selected actual _ | binary selected actual _ _
  | conditional selected actual _ _ _ =>
    cases Option.some.inj (selected.symm.trans found)
    simp [form] at actual

/-- Every stored direct-call path contradicts authentic legacy syntax at its
root. Children are followed through the exact original occurrence references. -/
theorem no_direct_of_syntax
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (root : Certificate policy body compilation readFuel values source context reasonAt scope id lowered)
    (tree : Syntax source id) : NoDirect root := by
  intro fuel callScope callId callee ids instantiation callCode compiler path
  induction path with
  | here calleeTyped application sequence children =>
    exact syntax_not_direct tree compiler.metadata.found compiler.form
  | @group scope id node inner innerNode code actual form found sourceType child inside ih =>
    exact ih (syntax_child tree actual.found (by simp [form, ExpressionForm.references]))
  | @tuple_child scope id node tupleIds types codes header sequence children child childCode member inside ih =>
    exact ih (syntax_child tree header.metadata.found (by
      simp [header.form, ExpressionForm.references, (List.of_mem_zip member).1]))
  | @constructor_child scope id node instantiation constructorIds tag headerWord codes header form admissible ranges count nodes sequence children child childCode member inside ih =>
    exact ih (syntax_child tree header.metadata.found (by
      simp [form, ExpressionForm.references, (List.of_mem_zip member).1]))
  | @direct_child scope id otherCallee otherIds instantiation otherFuel code types outer calleeTyped application sequence children child childCode member inside ih =>
    exact syntax_not_direct tree outer.metadata.found outer.form
  | @call_child scope id otherCallee otherIds metadata otherFuel code types outer sequence children child childCode member inside ih =>
    apply ih
    apply syntax_child tree outer.found
    rcases List.mem_cons.mp member with same | remaining
    · cases same
      simp [outer.originalForm, ExpressionForm.references]
    · simp [outer.originalForm, ExpressionForm.references, (List.of_mem_zip remaining).1]
  | @unary_child scope id node operand childNode operator operandType resultType core childCode metadata form found inputType outputType profile child inside ih =>
    exact ih (syntax_child tree metadata.found (by simp [form, ExpressionForm.references]))
  | @binary_left scope id node left right leftNode rightNode operator operandType resultType mode leftCode rightCode metadata form leftFound rightFound leftType rightType outputType profile first second inside ih =>
    exact ih (syntax_child tree metadata.found (by simp [form, ExpressionForm.references]))
  | @binary_right scope id node left right leftNode rightNode operator operandType resultType mode leftCode rightCode metadata form leftFound rightFound leftType rightType outputType profile first second inside ih =>
    exact ih (syntax_child tree metadata.found (by simp [form, ExpressionForm.references]))
  | @conditional_condition scope id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree inside ih =>
    exact ih (syntax_child tree metadata.found (by simp [form, ExpressionForm.references]))
  | @conditional_then scope id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree inside ih =>
    exact ih (syntax_child tree metadata.found (by simp [form, ExpressionForm.references]))
  | @conditional_else scope id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree inside ih =>
    exact ih (syntax_child tree metadata.found (by simp [form, ExpressionForm.references]))

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRecursiveCallerSyntax
