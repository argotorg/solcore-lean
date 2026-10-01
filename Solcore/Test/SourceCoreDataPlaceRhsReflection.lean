import Solcore.SourceSemantics.CoreLowering.DataPlaceRhsReflection
import Solcore.SourceSemantics.CoreLowering.Literals

/-! An actual lowered Boolean RHS is reflected under the three temporary
reference/key/snapshot slots. The universal child theorem reconstructs the
source value; the remaining modifier/write continuation is an output witness. -/
set_option autoImplicit false
namespace Tests.SourceCoreDataPlaceRhsReflection
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open SourceCoreDataPlaces DataPayload GenericExpressionMeaning

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"rhs_reflection", by decide⟩], by decide⟩⟩, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "rhs_reflection.solc"⟩, 0, 1⟩
private def binder : TypedBinder := ⟨⟨owner, 0⟩, "target", .mono .bool, [], false, none⟩
private def id : ExpressionId := ⟨⟨owner, 0⟩⟩
private def node : ExpressionNode := { id, span, type := .bool, form := .reference "true" (.builtinBoolean true) }
private def source : TypedSource := { owner, inputs := [binder], roots := [.expression id], nodes := [.expression node] }
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def catalog : SourceCoreDataCatalog.Catalog := {}
private def checked : SourceCoreDataCatalog.Checked := ⟨catalog, DataEnvironment.isWellFormed_sound (by decide)⟩
private def functions : GenericHeap.PayloadModel catalog where
  Represents := fun _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  extend := fun impossible _ _ => False.elim impossible
private def model := payloadModel catalog signatures functions
private theorem functionTypes : FunctionRuntimeTypes functions := fun impossible => False.elim impossible
private theorem observations : FunctionObservations catalog signatures functions (fun _ _ => False) := fun impossible => False.elim impossible
private theorem faithful : DataEquality.IdentityFaithful (fun _ _ => False) := by constructor <;> intros <;> contradiction
private theorem layouts : CatalogLayouts catalog := by constructor <;> intros <;> contradiction
private def sourceContext := (SourceSemantics.Context.ofSignatures signatures).withLocal binder.id binder.scheme
private def scope : Scope := [(binder.id, .bool)]
private def place : PlaceResolution := ⟨binder.id, [], .bool⟩
private def prepared : Prepared := ⟨⟨.bool, .bool, .bool, [], none⟩, [], [], Word.zero⟩
private def code : SourceCoreBasic.LoweredExpr := ⟨.bool, LanguageResult.success (.bool true)⟩
private inductive Child : Certificate where
  | literal (scope : Scope) : Child scope id code
private def faults : FaultRep := fun _ _ => True
private theorem found : source.lookupExpression? id = some node := by cbv
private theorem literal : Literals.Tree source id (.bool true) 1 :=
  .bool (lookupExpression?_sound found) rfl rfl rfl rfl
private theorem meaning (program : SourceSemantics.Program) :
    Reflects model program sourceContext [] source Child faults := by
  intro localScope expression lowered certified selected selectedBy mapping world admin environment canonical actual
    before store ξ value after environments heaps locals layout evaluated
  cases certified
  have same := Option.some.inj (selectedBy.symm.trans found)
  subst selected
  simp only [code, LanguageResult.success, Expr.rename] at evaluated
  cases evaluated with
  | inRight evaluated =>
    cases evaluated
    exact ⟨.value (.bool true), before, mapping, world,
      .value (literal.source_evaluates program sourceContext [] environment before), .value (.bool true), heaps,
      .refl _, .refl _, .refl _ _, .refl _⟩

example : SourceCoreBasic.lowerExpression 3 source scope id Word.zero = .ok code := by cbv
private def heap : Dynamic.Heap := ⟨[⟨.bool, none, none⟩]⟩
private def store : Store := [.inLeft .bool .unit, .integer 900]
private def world : StoreTyping := [OptionalCell.cellType .bool, .integer]
private def sourceEnvironment : Dynamic.Environment := [(binder.id, ⟨0⟩)]
private def environment : Environment := [.cellRef (OptionalCell.cellType .bool) 0]
private theorem heapRelated : GenericHeap.HeapRepresents model [0] world heap store := by
  have empty : GenericHeap.HeapRepresents model [] [] ⟨[]⟩ [] := .empty
  exact (empty.allocate (.uninitialized rfl) .append).1.allocate_administrative .integer
private theorem environments : DataHeap.EnvRepresents catalog [0] world [] scope sourceEnvironment environment :=
  .cons ⟨rfl, rfl⟩ (.nil .nil)
private theorem locals : Dynamic.EnvironmentAgrees heap sourceContext.locals sourceEnvironment :=
  .cons (.intro .head) rfl (.ordinary rfl rfl) .nil
private theorem targetLayout : DataPlaceResolvedTarget.Layout checked signatures functions source Child scope place prepared [] []
    (SourceCoreLocalCell.coreContext scope ++ []) := by
  refine ⟨.nil, rfl, .ordinary ?_ rfl, ?_, infer_sound (by decide)⟩
  · intro impossible; obtain ⟨_, _, same⟩ := impossible; cases same
  · intro mapping world sources values projections shaped related
    cases shaped
    exact ⟨0, .nil rfl⟩
private def expression : Expr := execute prepared (.var 0) (SourceCoreCalls.packArguments []) code.expression
  (LanguageResult.success .unit) .unit none false Word.zero
example : lower checked signatures (fun fuel source scope id reasonAt =>
    SourceCoreBasic.lowerExpression fuel source scope id (reasonAt id)) 3 source scope (.occurrence id.occurrence)
    ⟨place, []⟩ .equal (some id) .unit (LanguageResult.success .unit) (fun _ => Word.zero)
    Word.zero Word.zero (fun _ => Word.zero) = .ok expression := by cbv
example : infer? (SourceCoreLocalCell.coreContext scope) expression catalog.definitions =
    some (LanguageResult.resultType .unit) := by cbv
private def finalStore : Store := [.inRight .unit (.bool true), .integer 900]
private theorem ran : runStateful 100 (.initial expression environment store) = .done (.inRight .word .unit) finalStore := by cbv

private theorem reflected (program : SourceSemantics.Program) :
    DataPlaceRhsReflection.Result checked signatures functions program sourceContext [] source faults prepared [] [] place
      sourceEnvironment environment heap store [0] world id code (LanguageResult.success .unit) .unit .equal Word.zero
      (.inRight .word .unit) finalStore := by
  have resolution := DataPlacePrefixReflection.reflects (checked := checked) targetLayout
    (steps := []) (.nil rfl) (fuel := 5) (missing := fun _ => Word.zero) (.nil 0)
    (meaning program) functionTypes layouts observations faithful (fun _ => trivial) environments heapRelated locals rfl
    .head (.intro .head) rfl trivial (runStateful_evaluation_sound ran)
  exact DataPlaceRhsReflection.reflects (meaning program) (Child.literal scope) found rfl rfl environments locals resolution

/-- The actual source target and RHS trace are both obtained from the whole
Core run. The RHS's Core value is still related after its own heap effects. -/
example (program : SourceSemantics.Program) : ∃ target targetHeap, ∃ resolution : DataPlaceResolvedTarget.Execution checked signatures functions prepared [] [] place target
      environment store [0] world heap targetHeap, ∃ right : DataPlaceRhsReflection.Execution checked signatures functions program sourceContext [] source sourceEnvironment
      prepared [] [] place target environment store [0] world heap targetHeap resolution id code,
    Dynamic.SourcePlaceResolves program sourceContext [] source sourceEnvironment heap place target targetHeap ∧
    Dynamic.ExpressionEvaluates program sourceContext [] source sourceEnvironment targetHeap id right.right right.heap ∧
    ValueRep catalog signatures functions right.mapping right.world .bool right.right right.value .bool ∧
    Evaluates (DataPlaceExecution.rhsEnvironment prepared.route.rootType resolution.target
      (DataPatternValues.packValues resolution.values) resolution.snapshot right.value environment) right.store
      (DataPlaceRhsReflection.remainder prepared .unit (LanguageResult.success .unit) .unit none Word.zero)
      (.inRight .word .unit) finalStore := by
  have result := reflected program
  cases result with
  | fault sourceFault resultEq => cases resultEq
  | ready sourceTrace resolution right continuation =>
    exact ⟨_, _, resolution, right, sourceTrace, right.sourceTrace, right.related, continuation⟩

end Tests.SourceCoreDataPlaceRhsReflection
