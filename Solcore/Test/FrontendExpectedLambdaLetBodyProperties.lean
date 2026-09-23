import Solcore.Frontend.Expected
import Solcore.Frontend.RecursiveComputationReturnTree
import Solcore.Frontend.RecursiveLocalComputation

/-! Original source typing precedes elaboration and checking. The leading new f
captures the old f in its initializer scope; only the original tail sees new f.
Arbitrary outer rows and well-formed component types need no runtime inhabitants. -/
set_option autoImplicit false
namespace Tests.FrontendExpectedLambdaLetBody
open Solcore Solcore.Frontend
private structure Scenario where
  span : Syntax.SourceSpan
  owner : Resolved.DeclarationId
  outer : LocalTypeInputs
  a : Core.Ty
  b : Core.Ty
  depth : Nat
  typedParameter : Bool
  domain : Core.Ty.WellFormed [] a
  codomain : Core.Ty.WellFormed [] b
private def fn (p : Scenario) : Core.Ty := .function p.a p.b
private def types (p : Scenario) : TypeNameTable := [(["F"],fn p),(["F"],.bool),(["A"],p.a)]
private def named (p : Scenario) (name : String) : Syntax.TypeExpr :=
  ⟨p.span,.named ⟨p.span,⟨⟨⟨p.span,name⟩,[]⟩⟩⟩ none⟩
private def ref (p : Scenario) (name : String) : Syntax.Expr := ⟨p.span,.identifier ⟨p.span,name⟩⟩
private def call (p : Scenario) (argument : String) : Syntax.Expr :=
  ⟨p.span,.call (ref p "f") ⟨p.span,[ref p argument]⟩⟩
private def argumentScope (p : Scenario) := p.outer.bindFresh p.owner "y" p.a
private def initial (p : Scenario) := (argumentScope p).bindFresh p.owner "f" (fn p)
private def oldId (p : Scenario) := Resolved.freshLocalId p.owner (argumentScope p).ids
private def nextId (p : Scenario) := Resolved.freshLocalId p.owner (initial p).ids
private def lambdaInputs (p : Scenario) := (initial p).bindFresh p.owner "x" p.a
private def tailInputs (p : Scenario) : Nat → LocalTypeInputs
  | 0 => (initial p).bindFresh p.owner "f" (fn p)
  | n+1 => (tailInputs p n).bindFresh p.owner "y" p.a
private def lambdaBody (p : Scenario) : Syntax.Block := ⟨p.span,[⟨p.span,.returnStmt (some (call p "x"))⟩]⟩
private def initializer (p : Scenario) : Syntax.Expr :=
  ⟨p.span,.lambda p.span ⟨p.span,[⟨p.span,if p.typedParameter then
    .typed none ⟨p.span,"x"⟩ (named p "A") else .inferred ⟨p.span,"x"⟩⟩]⟩ none (lambdaBody p)⟩
private def tailStatements (p : Scenario) : Nat → List Syntax.Statement
  | 0 => [⟨p.span,.returnStmt (some (call p "y"))⟩]
  | n+1 => ⟨p.span,.letDecl ⟨p.span,"y"⟩ (some (named p "A")) (some (ref p "y"))⟩::
      ⟨p.span,.letDecl ⟨p.span,"y"⟩ none (some (ref p "y"))⟩::tailStatements p n
private def source (p : Scenario) : Syntax.Block :=
  ⟨p.span,⟨p.span,.letDecl ⟨p.span,"f"⟩ (some (named p "F")) (some (initializer p))⟩::tailStatements p p.depth⟩
private theorem aMeaning (p : Scenario) : StructuralTypeDenotes (types p) (named p "A") p.a :=
  .named (.tail (by change (["F"] : List String) ≠ ["A"]; decide)
    (.tail (by change (["F"] : List String) ≠ ["A"]; decide) .head))
private theorem freshNeOld (p : Scenario) : nextId p ≠ oldId p :=
  Resolved.freshLocalId_cons_fresh_ne p.owner (argumentScope p).ids
private theorem lambdaTyped (p : Scenario) :
    ExpectedComputationLambdaHasType RecursiveLocalComputationHasType (types p) p.owner (initial p) (initializer p) (fn p) := by
  have header : ExpectedUnaryLambdaHeaderDeclares (types p) p.owner (initial p) (initializer p) (fn p)
      ⟨lambdaInputs p,lambdaBody p,p.a,p.b⟩ := by
    cases typed : p.typedParameter
    · simp only [initializer,typed,Bool.false_eq_true,ite_false]; exact .lambda .inferred .omitted
    · simp only [initializer,typed,ite_true]; exact .lambda (.typed (aMeaning p)) .omitted
  exact .lambda header p.domain p.codomain (.expression (.application
    (.pure (.identifier (.tail (by change "x" ≠ "f"; decide) .head) (.tail (freshNeOld p) .head)))
    (.pure (.identifier .head .head))))
private theorem tailFunction (p : Scenario) (m : Nat) :
    LocalNameTable.Lookup (tailInputs p m).names "f" (nextId p) ∧
    Resolved.LocalScope.Lookup (tailInputs p m).context (nextId p) (fn p) := by
  induction m with
  | zero => exact ⟨.head,.head⟩
  | succ m ih =>
      have different : Resolved.freshLocalId p.owner (tailInputs p m).ids ≠ nextId p := by
        intro same
        have member : nextId p ∈ (tailInputs p m).names.map Prod.snd :=
          List.mem_map.mpr ⟨("f",nextId p),ih.1.mem,rfl⟩
        rw [LocalTypeInputs.names_ids] at member
        exact Resolved.freshLocalId_not_mem p.owner _ (same ▸ member)
      exact ⟨.tail (by change "y" ≠ "f"; decide) ih.1,.tail different ih.2⟩
private theorem tailArgument (p : Scenario) (m : Nat) :
    RecursiveLocalComputationHasType (tailInputs p m).names (tailInputs p m).context (ref p "y") p.a := by
  cases m with
  | zero =>
      have newNeArgument : nextId p ≠ Resolved.freshLocalId p.owner p.outer.ids := by
        intro same
        apply Resolved.freshLocalId_not_mem p.owner (initial p).ids
        change nextId p ∈ (initial p).ids
        rw [same]
        simp [initial,argumentScope]
      exact .pure (.identifier
        (.tail (by change "f" ≠ "y"; decide) (.tail (by change "f" ≠ "y"; decide) .head))
        (.tail newNeArgument (.tail (Resolved.freshLocalId_cons_fresh_ne p.owner p.outer.ids) .head)))
  | succ m => exact .pure (.identifier .head .head)
private theorem tailTyped (p : Scenario) (n m : Nat) :
    RecursiveComputationReturnTreeHasType (types p) p.owner (tailInputs p m) ⟨p.span,tailStatements p n⟩ p.b := by
  induction n generalizing m with
  | zero => exact .expression (.application
      (.pure (.identifier (tailFunction p m).1 (tailFunction p m).2)) (tailArgument p m))
  | succ n ih =>
      exact .binding (aMeaning p) (tailArgument p m) (.inferred (tailArgument p (m+1)) (ih (m+2)))
private theorem original (p : Scenario) :
    ExpectedLambdaLetBodyHasType RecursiveLocalComputationHasType (types p) p.owner (initial p) (source p) p.b :=
  .binding (.named .head) (lambdaTyped p) (tailTyped p p.depth 0)

theorem original_source_typing_checks_the_initializer_before_the_outer_binding (p : Scenario) :
    ExpectedComputationLambdaHasType RecursiveLocalComputationHasType (types p) p.owner (initial p) (initializer p) (fn p) ∧
      RecursiveComputationReturnTreeHasType (types p) p.owner (tailInputs p 0) ⟨p.span,tailStatements p p.depth⟩ p.b ∧
      ExpectedLambdaLetBodyHasType RecursiveLocalComputationHasType (types p) p.owner (initial p) (source p) p.b :=
  ⟨lambdaTyped p,tailTyped p p.depth 0,original p⟩
theorem an_independent_elaboration_exists_only_after_source_typing (p : Scenario) :
    ∃ core,ExpectedLambdaLetBodyElaborates RecursiveLocalComputationElaborates (types p) p.owner (initial p) (source p) core p.b :=
  (expectedLambdaLetBodyHasType_iff_elaborates recursiveLocalComputationHasType_iff_elaborates).mp (original p)
theorem the_existing_child_checker_matches_the_independent_source_result (p : Scenario) :
    ∃ core,elaborateExpectedLambdaLetBody? elaborateRecursiveLocalComputation? (types p) p.owner (initial p) (source p)=some (core,p.b) ∧
      ExpectedLambdaLetBodyElaborates RecursiveLocalComputationElaborates (types p) p.owner (initial p) (source p) core p.b := by
  obtain ⟨core,checked⟩ := (expectedLambdaLetBodyHasType_iff_checked recursiveLocalComputationHasType_iff_elaborates
    elaborateRecursiveLocalComputation?_iff).mp (original p)
  exact ⟨core,checked,(elaborateExpectedLambdaLetBody?_iff elaborateRecursiveLocalComputation?_iff).mp checked⟩
theorem core_typing_of_independent_elaboration_needs_no_checker_premise
    (table : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs)
    (source : Syntax.Block) (core : Core.Expr) (type : Core.Ty)
    (e : ExpectedLambdaLetBodyElaborates RecursiveLocalComputationElaborates table owner inputs source core type) :
    Core.HasType inputs.context.values core type := e.core_hasType RecursiveLocalComputationElaborates.core_hasType
theorem either_witness_recovers_source_typing_without_runtime_arguments
    (table : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs) (source : Syntax.Block) (type : Core.Ty) :
    ((∃ core,ExpectedLambdaLetBodyElaborates RecursiveLocalComputationElaborates table owner inputs source core type) →
      ExpectedLambdaLetBodyHasType RecursiveLocalComputationHasType table owner inputs source type) ∧
    ((∃ core,elaborateExpectedLambdaLetBody? elaborateRecursiveLocalComputation? table owner inputs source=some (core,type)) →
      ExpectedLambdaLetBodyHasType RecursiveLocalComputationHasType table owner inputs source type) :=
  ⟨(expectedLambdaLetBodyHasType_iff_elaborates recursiveLocalComputationHasType_iff_elaborates).mpr,
    (expectedLambdaLetBodyHasType_iff_checked recursiveLocalComputationHasType_iff_elaborates elaborateRecursiveLocalComputation?_iff).mpr⟩
theorem function_alias_first_match_is_resolved_before_same_name_term_shadowing (p : Scenario) :
    StructuralTypeDenotes (types p) (named p "F") (fn p) ∧
      interpretStructuralType? (types p) (named p "F")=some (fn p) ∧
      (types p).lookup? ["F"]≠some .bool := by
  refine ⟨.named .head,(interpretStructuralType?_iff).mpr (.named .head),?_⟩
  simp [types,TypeNameTable.lookup?,fn]
theorem identical_fresh_numbers_belong_to_disjoint_parameter_and_outer_let_scopes (p : Scenario) :
    (lambdaInputs p).names=("x",nextId p)::(initial p).names ∧
      (tailInputs p 0).names=("f",nextId p)::(initial p).names ∧
      (lambdaInputs p).ids=(tailInputs p 0).ids ∧
      (lambdaInputs p).bindings.tail=(initial p).bindings ∧
      (tailInputs p 0).bindings.tail=(initial p).bindings ∧
      nextId p ∉ (initial p).ids :=
  ⟨rfl,rfl,rfl,rfl,rfl,Resolved.freshLocalId_not_mem p.owner (initial p).ids⟩
theorem initializer_f_is_the_old_row_but_the_tail_f_is_the_new_head (p : Scenario) :
    LocalNameTable.Lookup (lambdaInputs p).names "f" (oldId p) ∧
      Resolved.LocalScope.IndexOf (lambdaInputs p).context.ids (oldId p) 1 ∧
      LocalNameTable.Lookup (tailInputs p 0).names "f" (nextId p) ∧
      Resolved.LocalScope.IndexOf (tailInputs p 0).context.ids (nextId p) 0 ∧
      nextId p ≠ oldId p :=
  ⟨.tail (by change "x" ≠ "f"; decide) .head,.tail (freshNeOld p) .head,.head,.head,freshNeOld p⟩
theorem fresh_selection_ignores_an_arbitrarily_high_foreign_owner_row
    (p : Scenario) (foreign : Resolved.LocalId) (different : foreign.owner≠p.owner) :
    Resolved.freshLocalId p.owner (foreign::(initial p).ids)=nextId p :=
  Resolved.freshLocalId_cons_of_ne_owner p.owner (initial p).ids foreign different
theorem provenance_keeps_original_initializer_and_tail_scopes_separate
    (table : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs)
    (source : Syntax.Block) (core : Core.Expr) (type : Core.Ty)
    (e : ExpectedLambdaLetBodyElaborates RecursiveLocalComputationElaborates table owner inputs source core type) :
    ∃ name : Syntax.Identifier, ∃ declaredType initializer rest blockSpan initializerCore tailCore,
      ExpectedComputationLambdaElaborates RecursiveLocalComputationElaborates table owner inputs initializer initializerCore declaredType ∧
      ComputationReturnTreeElaborates RecursiveLocalComputationElaborates table owner
        (inputs.bindFresh owner name.value declaredType) ⟨blockSpan,rest⟩ tailCore type ∧
      core=.letE initializerCore tailCore ∧ (inputs.bindFresh owner name.value declaredType).bindings.tail=inputs.bindings := by
  obtain ⟨bs,_,name,_,init,rest,decl,ic,tc,_,_,initializer,tail,shape,_⟩ := e.provenance
  exact ⟨name,decl,init,rest,bs,ic,tc,initializer,tail,shape,rfl⟩
theorem omitting_the_outer_let_annotation_remains_outside_this_adapter (p : Scenario) :
    let inferred : Syntax.Block := ⟨p.span,⟨p.span,.letDecl ⟨p.span,"f"⟩ none (some (initializer p))⟩::tailStatements p p.depth⟩
    elaborateExpectedLambdaLetBody? elaborateRecursiveLocalComputation? (types p) p.owner (initial p) inferred=none ∧
      (¬∃ core type,ExpectedLambdaLetBodyElaborates RecursiveLocalComputationElaborates (types p) p.owner (initial p) inferred core type) ∧
      (¬∃ type,ExpectedLambdaLetBodyHasType RecursiveLocalComputationHasType (types p) p.owner (initial p) inferred type) := by
  dsimp only
  refine ⟨rfl,?_,?_⟩
  · exact (elaborateExpectedLambdaLetBody?_eq_none_iff elaborateRecursiveLocalComputation?_iff).mp rfl
  · rintro ⟨type,typed⟩; cases typed

end Tests.FrontendExpectedLambdaLetBody
