import Solcore.Frontend.Expected
import Solcore.Frontend.RecursiveComputationReturnTree
import Solcore.Frontend.Computation
import Solcore.Frontend.RecursiveLocalComputation

/-! Original symbolic headers retain every supplied range and outer row. Header
meaning precedes executable checking and requires no runtime inhabitants. The
separate return-body examples do not elaborate or evaluate a source lambda. -/
set_option autoImplicit false
namespace Tests.FrontendExpectedLambdaHeader
open Solcore Solcore.Frontend
private structure Written where
  sourceSpan : Syntax.SourceSpan
  keyword : Syntax.SourceSpan
  parametersSpan : Syntax.SourceSpan
  parameterSpan : Syntax.SourceSpan
  name : Syntax.Identifier
  body : Syntax.Block
private def source (w : Written) (parameter : Syntax.LambdaParameterValue) (returns : Option Syntax.TypeExpr) : Syntax.Expr :=
  ⟨w.sourceSpan,.lambda w.keyword ⟨w.parametersSpan,[⟨w.parameterSpan,parameter⟩]⟩ returns w.body⟩
private def inferred (w : Written) : Syntax.Expr := source w (.inferred w.name) none
private def result (w : Written) (o : Resolved.DeclarationId) (i : LocalTypeInputs) (a b : Core.Ty) : DeclaredUnaryLambdaHeader :=
  ⟨i.bindFresh o w.name.value a,w.body,a,b⟩
private theorem original (types : TypeNameTable) (w : Written) (o : Resolved.DeclarationId)
    (i : LocalTypeInputs) (a b : Core.Ty) :
    ExpectedUnaryLambdaHeaderDeclares types o i (inferred w) (.function a b) (result w o i a b) :=
  .lambda .inferred .omitted
private def named (span : Syntax.SourceSpan) (name : String) : Syntax.TypeExpr :=
  ⟨span,.named ⟨span,⟨⟨⟨span,name⟩,[]⟩⟩⟩ none⟩

theorem arbitrary_expected_components_need_neither_annotations_nor_runtime_inhabitants
    (types : TypeNameTable) (w : Written) (o : Resolved.DeclarationId) (i : LocalTypeInputs) (a b : Core.Ty) :
    ExpectedUnaryLambdaHeaderDeclares types o i (inferred w) (.function a b) (result w o i a b) ∧
      declareExpectedUnaryLambdaHeader? types o i (inferred w) (.function a b)=some (result w o i a b) ∧
      (result w o i a b).body=w.body ∧ (result w o i a b).returnType=b :=
  ⟨original types w o i a b,declareExpectedUnaryLambdaHeader?_iff.mpr (original types w o i a b),rfl,rfl⟩
theorem explicit_and_inferred_original_headers_have_the_same_exact_inner_record
    (types : TypeNameTable) (w : Written) (o : Resolved.DeclarationId) (i : LocalTypeInputs) (a b : Core.Ty)
    (parameterAnnotation returnAnnotation : Syntax.TypeExpr)
    (pa : StructuralTypeDenotes types parameterAnnotation a) (ra : StructuralTypeDenotes types returnAnnotation b) :
    ExpectedUnaryLambdaHeaderDeclares types o i (source w (.typed none w.name parameterAnnotation) (some returnAnnotation))
      (.function a b) (result w o i a b) ∧
      declareExpectedUnaryLambdaHeader? types o i (source w (.typed none w.name parameterAnnotation) (some returnAnnotation)) (.function a b)=
        declareExpectedUnaryLambdaHeader? types o i (inferred w) (.function a b) := by
  have explicit : ExpectedUnaryLambdaHeaderDeclares types o i
      (source w (.typed none w.name parameterAnnotation) (some returnAnnotation)) (.function a b) (result w o i a b) :=
    .lambda (.typed pa) (.annotated ra)
  exact ⟨explicit,(declareExpectedUnaryLambdaHeader?_iff.mpr explicit).trans
    (declareExpectedUnaryLambdaHeader?_iff.mpr (original types w o i a b)).symm⟩
theorem every_independent_result_is_the_original_body_with_one_fresh_row
    (types : TypeNameTable) (w : Written) (o : Resolved.DeclarationId) (i : LocalTypeInputs) (a b : Core.Ty)
    (out : DeclaredUnaryLambdaHeader)
    (evidence : ExpectedUnaryLambdaHeaderDeclares types o i (inferred w) (.function a b) out) :
    out=result w o i a b ∧ out.body=w.body ∧ out.inputs.bindings=
      {name:=w.name.value,id:=Resolved.freshLocalId o i.ids,type:=a}::i.bindings ∧
      Resolved.freshLocalId o i.ids ∉ i.ids := by
  have same := evidence.result_unique (original types w o i a b)
  rw [same]
  exact ⟨rfl,rfl,rfl,Resolved.freshLocalId_not_mem o i.ids⟩
theorem provenance_contains_original_syntax_and_both_expected_components
    (types : TypeNameTable) (o : Resolved.DeclarationId) (i : LocalTypeInputs)
    (src : Syntax.Expr) (expected : Core.Ty) (out : DeclaredUnaryLambdaHeader)
    (evidence : ExpectedUnaryLambdaHeaderDeclares types o i src expected out) :
    ∃ sourceSpan keyword parametersSpan parameter returns, ∃ name : Syntax.Identifier,
      src=⟨sourceSpan,.lambda keyword ⟨parametersSpan,[parameter]⟩ returns out.body⟩ ∧
      expected=.function out.parameterType out.returnType ∧
      ExpectedLambdaReturnDenotes types returns out.returnType ∧
      out.inputs=i.bindFresh o name.value out.parameterType := by
  obtain ⟨sp,kw,ps,p,ret,name,shape,expected,_,meaning,inputs,_⟩ := evidence.provenance_and_layout
  exact ⟨sp,kw,ps,p,ret,name,shape,expected,meaning,inputs⟩
theorem original_parameter_spelling_shadows_without_deleting_any_outer_binding
    (types : TypeNameTable) (w : Written) (o : Resolved.DeclarationId) (i : LocalTypeInputs) (a b : Core.Ty) :
    ExpectedUnaryLambdaHeaderDeclares types o i (inferred w) (.function a b) (result w o i a b) ∧
      LocalNameTable.Lookup (result w o i a b).inputs.names w.name.value (Resolved.freshLocalId o i.ids) ∧
      Resolved.LocalScope.Lookup (result w o i a b).inputs.context (Resolved.freshLocalId o i.ids) a ∧
      (result w o i a b).inputs.context.values=a::i.context.values ∧
      (result w o i a b).inputs.bindings.tail=i.bindings :=
  ⟨original types w o i a b,.head,.head,rfl,rfl⟩
theorem annotation_meanings_keep_first_match_priority_even_under_same_spelling_shadow
    (w : Written) (o : Resolved.DeclarationId) (i : LocalTypeInputs) (a b hidden : Core.Ty) :
    let table : TypeNameTable := [([w.name.value],a),([w.name.value],hidden)]
    declareExpectedUnaryLambdaHeader? table o i
      (source w (.typed none w.name (named w.name.span w.name.value)) none) (.function a b)=some (result w o i a b) :=
  declareExpectedUnaryLambdaHeader?_iff.mpr (.lambda (.typed (.named .head)) .omitted)
theorem explicit_return_disagreement_has_no_header_derivation
    (types : TypeNameTable) (w : Written) (o : Resolved.DeclarationId) (i : LocalTypeInputs)
    (a actual expected : Core.Ty) (annotation : Syntax.TypeExpr)
    (meaning : StructuralTypeDenotes types annotation actual) (different : actual≠expected) :
    declareExpectedUnaryLambdaHeader? types o i (source w (.inferred w.name) (some annotation)) (.function a expected)=none ∧
      ¬ ∃ out,ExpectedUnaryLambdaHeaderDeclares types o i (source w (.inferred w.name) (some annotation)) (.function a expected) out := by
  have absent : ¬ ∃ out,ExpectedUnaryLambdaHeaderDeclares types o i
      (source w (.inferred w.name) (some annotation)) (.function a expected) out := by
    rintro ⟨out,evidence⟩
    cases evidence with
    | lambda _ returns => cases returns with
      | annotated found => exact different (meaning.type_unique found)
  exact ⟨declareExpectedUnaryLambdaHeader?_eq_none_iff.mpr absent,absent⟩

private def returned (w : Written) : Syntax.Block :=
  ⟨w.body.span,[⟨w.body.span,.returnStmt (some ⟨w.name.span,.identifier w.name⟩)⟩]⟩
private theorem returnedElab (types : TypeNameTable) (w : Written) (o : Resolved.DeclarationId) (i : LocalTypeInputs) (a : Core.Ty) :
    RecursiveComputationReturnTreeElaborates types o (i.bindFresh o w.name.value a) (returned w) (.var 0) a :=
  .expression (.pure (.identifier .head) (.var .head) (.var .head))
theorem a_separate_original_body_proof_can_use_the_declared_parameter_but_is_not_a_lambda_proof
    (types : TypeNameTable) (w : Written) (o : Resolved.DeclarationId) (i : LocalTypeInputs) (a : Core.Ty) :
    let written := {w with body:=returned w}
    let out := result written o i a a
    ExpectedUnaryLambdaHeaderDeclares types o i (inferred written) (.function a a) out ∧
      RecursiveComputationReturnTreeElaborates types o out.inputs out.body (.var 0) a ∧
      elaborateRecursiveComputationReturnTree? types o out.inputs out.body=some (.var 0,a) ∧
      elaborateRecursiveLocalComputation? i.names i.context (inferred written)=none := by
  refine ⟨original types _ o i a a,returnedElab types w o i a,?_,?_⟩
  · exact (elaborateComputationReturnTree?_iff elaborateRecursiveLocalComputation?_iff).mpr (returnedElab types w o i a)
  · simp [inferred,source,elaborateRecursiveLocalComputation?,elaborateLocalExpression?,resolveLocalExpression?]
theorem an_omitted_return_annotation_does_not_check_the_actual_return_body
    (types : TypeNameTable) (w : Written) (o : Resolved.DeclarationId) (i : LocalTypeInputs) (a b : Core.Ty) (different : a≠b) :
    let written := {w with body:=returned w}
    let out := result written o i a b
    declareExpectedUnaryLambdaHeader? types o i (inferred written) (.function a b)=some out ∧
      ¬ ∃ core,RecursiveComputationReturnTreeElaborates types o out.inputs out.body core b := by
  refine ⟨declareExpectedUnaryLambdaHeader?_iff.mpr (original types _ o i a b),?_⟩
  rintro ⟨core,wrong⟩
  have right := (elaborateComputationReturnTree?_iff elaborateRecursiveLocalComputation?_iff).mpr (returnedElab types w o i a)
  have other := (elaborateComputationReturnTree?_iff elaborateRecursiveLocalComputation?_iff).mpr wrong
  change elaborateRecursiveComputationReturnTree? types o (i.bindFresh o w.name.value a) (returned w)=some (core,b) at other
  exact different (congrArg Prod.snd (Option.some.inj (right.symm.trans other)))
theorem an_explicit_error_body_is_retained_and_not_mistaken_for_a_checked_body
    (types : TypeNameTable) (w : Written) (o : Resolved.DeclarationId) (i : LocalTypeInputs) (a b : Core.Ty) :
    let written := {w with body:=⟨w.body.span,[⟨w.body.span,.error⟩]⟩}
    let out := result written o i a b
    declareExpectedUnaryLambdaHeader? types o i (inferred written) (.function a b)=some out ∧
      out.body=written.body ∧ elaborateRecursiveComputationReturnTree? types o out.inputs out.body=none ∧
      elaborateRecursiveLocalComputation? i.names i.context (inferred written)=none := by
  refine ⟨declareExpectedUnaryLambdaHeader?_iff.mpr (original types _ o i a b),rfl,?_,?_⟩
  · simp [result,elaborateRecursiveComputationReturnTree?,elaborateComputationReturnTree?]
  · simp [inferred,source,elaborateRecursiveLocalComputation?,elaborateLocalExpression?,resolveLocalExpression?]

private def owner : Resolved.DeclarationId := ⟨⟨.main,⟨[⟨"ExpectedLambdaHeader",by decide⟩],by decide⟩⟩,143⟩
private def foreign : Resolved.DeclarationId := {owner with declarationIndex:=144}
private def sparse (name : String) (a : Core.Ty) (high : Nat) : LocalTypeInputs :=
  ⟨[⟨name,⟨owner,7⟩,a⟩,⟨name,⟨foreign,high⟩,.bool⟩,⟨"old",⟨owner,2⟩,.word⟩],by simp [owner,foreign]⟩
theorem sparse_owner_indices_ignore_arbitrarily_large_foreign_rows
    (types : TypeNameTable) (w : Written) (a b oldType : Core.Ty) (high : Nat) :
    let outer := sparse w.name.value oldType high
    let out := result w owner outer a b
    ExpectedUnaryLambdaHeaderDeclares types owner outer (inferred w) (.function a b) out ∧
      out.inputs.ids=[⟨owner,8⟩,⟨owner,7⟩,⟨foreign,high⟩,⟨owner,2⟩] ∧
      out.inputs.bindings.map (fun row => (row.name,row.type))=
        [(w.name.value,a),(w.name.value,oldType),(w.name.value,.bool),("old",.word)] :=
  ⟨original types w owner _ a b,rfl,rfl⟩
end Tests.FrontendExpectedLambdaHeader
