import Solcore.Frontend.Expected
import Solcore.Frontend.RecursiveComputationReturnTree
import Solcore.Frontend.RecursiveLocalComputation
import Solcore.Frontend.LocalFunctionApplication
import Solcore.Core.FuelResumptionProperties

/-! Source-only typing is constructed before literal Core or checker evidence.
Each repeated f initializer sees the preceding f, never itself. Runtime paths
below concern only generated Core and keep every actual capture; no source evaluation is asserted. -/
set_option autoImplicit false
namespace Tests.FrontendExpectedLambdaLetSpine
open Solcore Solcore.Frontend
private structure Scenario where
  span : Syntax.SourceSpan
  owner : Resolved.DeclarationId
  outer : LocalTypeInputs
  a : Core.Ty
  b : Core.Ty
  domain : Core.Ty.WellFormed [] a
  codomain : Core.Ty.WellFormed [] b
private def fn (p : Scenario) : Core.Ty := .function p.a p.b
private def types (p : Scenario) : TypeNameTable := [(["F"],fn p),(["F"],.bool)]
private def annotation (p : Scenario) : Syntax.TypeExpr :=
  ⟨p.span,.named ⟨p.span,⟨⟨⟨p.span,"F"⟩,[]⟩⟩⟩ none⟩
private def ref (p : Scenario) (name : String) : Syntax.Expr := ⟨p.span,.identifier ⟨p.span,name⟩⟩
private def lambdaBody (p : Scenario) : Syntax.Block :=
  ⟨p.span,[⟨p.span,.returnStmt (some ⟨p.span,.call (ref p "f") ⟨p.span,[ref p "x"]⟩⟩)⟩]⟩
private def initializer (p : Scenario) : Syntax.Expr :=
  ⟨p.span,.lambda p.span ⟨p.span,[⟨p.span,.inferred ⟨p.span,"x"⟩⟩]⟩ none (lambdaBody p)⟩
private def rows (p : Scenario) : Nat → LocalTypeInputs
  | 0 => p.outer.bindFresh p.owner "f" (fn p)
  | n+1 => (rows p n).bindFresh p.owner "f" (fn p)
private def visible (p : Scenario) : Nat → Resolved.LocalId
  | 0 => Resolved.freshLocalId p.owner p.outer.ids
  | n+1 => Resolved.freshLocalId p.owner (rows p n).ids
private def ordinary (p : Scenario) : Nat → List Syntax.Statement
  | 0 => [⟨p.span,.returnStmt (some (ref p "f"))⟩]
  | m+1 => ⟨p.span,.letDecl ⟨p.span,"f"⟩ (some (annotation p)) (some (ref p "f"))⟩::
      ⟨p.span,.letDecl ⟨p.span,"f"⟩ none (some (ref p "f"))⟩::ordinary p m
private def statements (p : Scenario) : Nat → Nat → List Syntax.Statement
  | 0,m => ordinary p m
  | n+1,m => ⟨p.span,.letDecl ⟨p.span,"f"⟩ (some (annotation p)) (some (initializer p))⟩::statements p n m
private def source (p : Scenario) (n m : Nat) : Syntax.Block := ⟨p.span,statements p n m⟩
private theorem rowFacts (p : Scenario) (j : Nat) :
    LocalNameTable.Lookup (rows p j).names "f" (visible p j) ∧
    Resolved.LocalScope.Lookup (rows p j).context (visible p j) (fn p) ∧
    Resolved.LocalScope.IndexOf (rows p j).context.ids (visible p j) 0 := by
  cases j <;> exact ⟨.head,.head,.head⟩
private theorem different (p : Scenario) (j : Nat) :
    Resolved.freshLocalId p.owner (rows p j).ids ≠ visible p j := by
  cases j <;> exact Resolved.freshLocalId_cons_fresh_ne _ _
private theorem header (p : Scenario) (j : Nat) :
    ExpectedUnaryLambdaHeaderDeclares (types p) p.owner (rows p j) (initializer p) (fn p)
      ⟨(rows p j).bindFresh p.owner "x" p.a,lambdaBody p,p.a,p.b⟩ := .lambda .inferred .omitted
private theorem lambdaTyped (p : Scenario) (j : Nat) :
    ExpectedComputationLambdaHasType RecursiveLocalComputationHasType (types p) p.owner
      (rows p j) (initializer p) (fn p) :=
  .lambda (header p j) p.domain p.codomain (.expression (.application
    (.pure (.identifier (.tail (by change "x" ≠ "f"; decide) (rowFacts p j).1)
      (.tail (different p j) (rowFacts p j).2.1))) (.pure (.identifier .head .head))))
private theorem ordinaryTyped (p : Scenario) (m j : Nat) :
    RecursiveComputationReturnTreeHasType (types p) p.owner (rows p j) ⟨p.span,ordinary p m⟩ (fn p) := by
  induction m generalizing j with
  | zero => exact .expression (.pure (.identifier (rowFacts p j).1 (rowFacts p j).2.1))
  | succ m ih =>
      exact .binding (.named .head) (.pure (.identifier (rowFacts p j).1 (rowFacts p j).2.1))
        (.inferred (.pure (.identifier .head .head)) (ih (j+2)))
private theorem terminalFalse (p : Scenario) (m : Nat) : isExpectedLambdaLetHead (source p 0 m)=false := by
  cases m <;> rfl
private theorem original (p : Scenario) (n m j : Nat) :
    ExpectedLambdaLetSpineHasType RecursiveLocalComputationHasType (types p) p.owner (rows p j) (source p n m) (fn p) := by
  induction n generalizing j with
  | zero => exact .terminal (terminalFalse p m) (ordinaryTyped p m j)
  | succ n ih => exact .binding rfl (.named .head) (lambdaTyped p j) (ih (j+1))

theorem arbitrary_consecutive_heads_and_ordinary_tail_have_original_source_typing (p : Scenario) (n m : Nat) :
    ExpectedLambdaLetSpineHasType RecursiveLocalComputationHasType (types p) p.owner (rows p 0) (source p n m) (fn p) :=
  original p n m 0
theorem both_existence_laws_consume_source_typing_without_actual_inhabitants (p : Scenario) (n m : Nat) :
    (∃ core,ExpectedLambdaLetSpineElaborates RecursiveLocalComputationElaborates (types p) p.owner (rows p 0) (source p n m) core (fn p)) ∧
    (∃ core,elaborateExpectedLambdaLetSpine? elaborateRecursiveLocalComputation? (types p) p.owner (rows p 0) (source p n m)=some (core,fn p)) :=
  ⟨(expectedLambdaLetSpineHasType_iff_elaborates recursiveLocalComputationHasType_iff_elaborates).mp (original p n m 0),
    (expectedLambdaLetSpineHasType_iff_checked recursiveLocalComputationHasType_iff_elaborates elaborateRecursiveLocalComputation?_iff).mp (original p n m 0)⟩
theorem zero_heads_delegate_the_complete_ordinary_tail (p : Scenario) (m : Nat) :
    isExpectedLambdaLetHead (source p 0 m)=false ∧
    elaborateExpectedLambdaLetSpine? elaborateRecursiveLocalComputation? (types p) p.owner (rows p 0) (source p 0 m)=
      elaborateComputationReturnTree? elaborateRecursiveLocalComputation? (types p) p.owner (rows p 0) (source p 0 m) := by
  exact ⟨terminalFalse p m,by unfold elaborateExpectedLambdaLetSpine?; simp only [terminalFalse p m,ite_true]⟩

private def bodyCore : Core.Expr := .apply (.var 1) (.var 0)
private def ordinaryCore : Nat → Core.Expr
  | 0 => .var 0
  | m+1 => .letE (.var 0) (.letE (.var 0) (ordinaryCore m))
private def literalCore (a b : Core.Ty) : Nat → Nat → Core.Expr
  | 0,m => ordinaryCore m
  | n+1,m => .letE (.lambda a b bodyCore) (literalCore a b n m)
private theorem lambdaElab (p : Scenario) (j : Nat) :
    ExpectedComputationLambdaElaborates RecursiveLocalComputationElaborates (types p) p.owner
      (rows p j) (initializer p) (.lambda p.a p.b bodyCore) (fn p) :=
  .lambda (header p j) p.domain p.codomain (.expression (.application
    (.pure (.identifier (.tail (by change "x" ≠ "f"; decide) (rowFacts p j).1))
      (.var (.tail (different p j) (rowFacts p j).2.2)) (.var (.tail (different p j) (rowFacts p j).2.1)))
    (.pure (.identifier .head) (.var .head) (.var .head))))
private theorem ordinaryElab (p : Scenario) (m j : Nat) :
    RecursiveComputationReturnTreeElaborates (types p) p.owner (rows p j) ⟨p.span,ordinary p m⟩ (ordinaryCore m) (fn p) := by
  induction m generalizing j with
  | zero => exact .expression (.pure (.identifier (rowFacts p j).1) (.var (rowFacts p j).2.2) (.var (rowFacts p j).2.1))
  | succ m ih =>
      exact .binding (.named .head)
        (.pure (.identifier (rowFacts p j).1) (.var (rowFacts p j).2.2) (.var (rowFacts p j).2.1))
        (.inferred (.pure (.identifier .head) (.var .head) (.var .head)) (ih (j+2)))
private theorem literalElab (p : Scenario) (n m j : Nat) :
    ExpectedLambdaLetSpineElaborates RecursiveLocalComputationElaborates (types p) p.owner (rows p j)
      (source p n m) (literalCore p.a p.b n m) (fn p) := by
  induction n generalizing j with
  | zero => exact .terminal (terminalFalse p m) (ordinaryElab p m j)
  | succ n ih => exact .binding rfl (.named .head) (lambdaElab p j) (ih (j+1))

theorem literal_nested_core_is_independent_of_the_checker (p : Scenario) (n m : Nat) :
    ExpectedLambdaLetSpineElaborates RecursiveLocalComputationElaborates (types p) p.owner (rows p 0)
      (source p n m) (literalCore p.a p.b n m) (fn p) ∧
    Core.HasType (rows p 0).context.values (literalCore p.a p.b n m) (fn p) ∧
    elaborateExpectedLambdaLetSpine? elaborateRecursiveLocalComputation? (types p) p.owner (rows p 0)
      (source p n m)=some (literalCore p.a p.b n m,fn p) :=
  ⟨literalElab p n m 0,(literalElab p n m 0).core_hasType RecursiveLocalComputationElaborates.core_hasType,
    (elaborateExpectedLambdaLetSpine?_iff elaborateRecursiveLocalComputation?_iff).mpr (literalElab p n m 0)⟩
theorem each_lambda_looks_up_the_previous_f_while_the_next_tail_gets_the_new_f (p : Scenario) (j : Nat) :
    LocalNameTable.Lookup ((rows p j).bindFresh p.owner "x" p.a).names "f" (visible p j) ∧
    Resolved.LocalScope.IndexOf ((rows p j).bindFresh p.owner "x" p.a).context.ids (visible p j) 1 ∧
    LocalNameTable.Lookup (rows p (j+1)).names "f" (visible p (j+1)) ∧ visible p (j+1)≠visible p j :=
  ⟨.tail (by change "x" ≠ "f"; decide) (rowFacts p j).1,
    .tail (different p j) (rowFacts p j).2.2,.head,different p j⟩
theorem separate_scopes_reuse_the_fresh_number_without_leaking_parameter_rows (p : Scenario) (j : Nat) :
    ((rows p j).bindFresh p.owner "x" p.a).ids=(rows p (j+1)).ids ∧
    ((rows p j).bindFresh p.owner "x" p.a).names=("x",visible p (j+1))::(rows p j).names ∧
    (rows p (j+1)).names=("f",visible p (j+1))::(rows p j).names ∧
    (rows p (j+1)).bindings.tail=(rows p j).bindings ∧ visible p (j+1)∉(rows p j).ids :=
  ⟨rfl,rfl,rfl,rfl,Resolved.freshLocalId_not_mem _ _⟩
theorem owner_filtered_fresh_growth_and_alias_first_match (p : Scenario) (j : Nat)
    (foreign : Resolved.LocalId) (differentOwner : foreign.owner≠p.owner) :
    Resolved.freshLocalId p.owner (foreign::(rows p j).ids)=visible p (j+1) ∧
    (visible p (j+2)).binderIndex=(visible p (j+1)).binderIndex+1 ∧
    StructuralTypeDenotes (types p) (annotation p) (fn p) ∧ (types p).lookup? ["F"]=some (fn p) :=
  ⟨Resolved.freshLocalId_cons_of_ne_owner _ _ _ differentOwner,
    Resolved.freshLocalId_cons_fresh_binderIndex _ _,.named .head,rfl⟩
theorem one_layer_provenance_preserves_the_entire_recursive_tail (p : Scenario) (n m : Nat) :
    ∃ blockSpan letSpan name annotation initializer rest declaredType initCore tailCore,
      source p (n+1) m=⟨blockSpan,⟨letSpan,.letDecl name (some annotation) (some initializer)⟩::rest⟩ ∧
      ExpectedComputationLambdaElaborates RecursiveLocalComputationElaborates (types p) p.owner
        (rows p 0) initializer initCore declaredType ∧
      ExpectedLambdaLetSpineElaborates RecursiveLocalComputationElaborates (types p) p.owner
        ((rows p 0).bindFresh p.owner name.value declaredType) ⟨blockSpan,rest⟩ tailCore (fn p) ∧
      literalCore p.a p.b (n+1) m=.letE initCore tailCore := by
  rcases (literalElab p (n+1) m 0).provenance with ⟨impossible,_⟩ | head
  · cases impossible
  · obtain ⟨bs,ls,name,ann,init,rest,decl,ic,tc,_,shape,_,initializer,tail,coreShape,_⟩ := head
    exact ⟨bs,ls,name,ann,init,rest,decl,ic,tc,shape,initializer,tail,coreShape⟩

theorem old_one_head_evidence_embeds_when_its_original_tail_is_terminal
    (ChildElab : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Expr → Core.Ty → Prop)
    (table : TypeNameTable) (owner : Resolved.DeclarationId) (inputs : LocalTypeInputs)
    (source : Syntax.Block) (core : Core.Expr) (type : Core.Ty)
    (old : ExpectedLambdaLetBodyElaborates ChildElab table owner inputs source core type)
    (tailFalse : isExpectedLambdaLetHead ⟨source.span,source.value.tail⟩=false) :
    ExpectedLambdaLetSpineElaborates ChildElab table owner inputs source core type := by
  cases old with
  | binding meaning initializer tail =>
      refine .binding ?_ meaning initializer (.terminal tailFalse tail)
      cases initializer with
      | lambda header _ _ _ => cases header; rfl

private def wrap (a b : Core.Ty) (environment : Core.Environment) : Core.Value := .closure a b bodyCore environment
private def capturedResult (a b : Core.Ty) : Nat → Core.Value → Core.Environment → Core.Value
  | 0,value,_ => value
  | n+1,value,suffix => capturedResult a b n (wrap a b (value::suffix)) (value::suffix)
private theorem capturePath (a b : Core.Ty) (n : Nat) (value : Core.Value)
    (suffix : Core.Environment) (store : Core.Store) (k : List Core.Frame) :
    Core.Steps (3*n+1) ⟨.eval (literalCore a b n 0) (value::suffix),k,store⟩
      ⟨.ret (capturedResult a b n value suffix),k,store⟩ := by
  induction n generalizing value suffix with
  | zero => exact .cons (.var rfl) .refl
  | succ n ih =>
      have count : 3*(n+1)+1=1+(3*n+1)+2 := by omega
      rw [count]
      exact CostStepComposition.letE (.cons .lambda .refl) (ih _ _)

theorem generated_core_captures_all_actual_rows_without_running_any_initializer_body
    (a b : Core.Ty) (n : Nat) (value : Core.Value) (suffix : Core.Environment)
    (store : Core.Store) (k : List Core.Frame) :
    Core.Steps (3*n+1) ⟨.eval (literalCore a b n 0) (value::suffix),k,store⟩
      ⟨.ret (capturedResult a b n value suffix),k,store⟩ := capturePath a b n value suffix store k
theorem actual_saved_core_checkpoints_resume_the_same_nested_capture_chain
    (a b : Core.Ty) (n spent : Nat) (value : Core.Value) (suffix : Core.Environment)
    (store : Core.Store) (cp : Core.State)
    (exhausted : Core.runStateful spent (.initial (literalCore a b n 0) (value::suffix) store)=.outOfFuel cp) :
    spent<3*n+1 ∧ Core.Steps (3*n+1-spent) cp (.final (capturedResult a b n value suffix) store) ∧
    ∀ extra,Core.runStateful extra cp=Core.runStateful (spent+extra) (.initial (literalCore a b n 0) (value::suffix) store) := by
  have path := capturePath a b n value suffix store []
  exact ⟨(path.residual_of_outOfFuel exhausted).1,(path.residual_of_outOfFuel exhausted).2,Core.runStateful_resume exhausted⟩

end Tests.FrontendExpectedLambdaLetSpine
