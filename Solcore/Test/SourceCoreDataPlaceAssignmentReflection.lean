import Solcore.SourceSemantics.CoreLowering.DataPlaceContinuationReflection
import Solcore.SourceSemantics.CoreLowering.Literals

/-! The real lowering and completed Core run yield an independently specified
source assignment. Universal child reflection supplies the source RHS; the
terminal continuation is eliminated after the actual seven-slot write prefix. -/
set_option autoImplicit false
set_option maxRecDepth 16384
namespace Tests.SourceCoreDataPlaceAssignmentReflection
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
    DataPlaceTailReflection.Result checked signatures functions program sourceContext [] source faults place .equal id
      sourceEnvironment environment heap store [0] world (LanguageResult.success .unit) .unit
      (.inRight .word .unit) finalStore := by
  exact DataPlaceAssignmentReflection.reflects (checked := checked) targetLayout
    (steps := []) (.nil rfl) (fuel := 5) (missing := fun _ => Word.zero) (.nil 0)
    (meaning program) functionTypes layouts observations faithful (fun _ => trivial)
    (Child.literal scope) found rfl rfl (Or.inl rfl) trivial (infer_sound (by decide))
    environments heapRelated locals rfl .head (.intro .head) rfl trivial
    (runStateful_evaluation_sound ran)

example (program : SourceSemantics.Program) : ∃ updated after finalMap finalWorld,
    Dynamic.SourcePlaceAssignment program sourceContext [] source (Dynamic.AssignmentValueApplies .equal)
      sourceEnvironment heap place id updated after ∧
    GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
    GeneralHeap.LocationMap.Extends [0] finalMap ∧ WorldExtends world finalWorld ∧
    GeneralHeap.AdministrativePreserved [0] store finalMap finalStore ∧
    Dynamic.HeapMetadataExtend heap after := by
  cases reflected program with
  | fault sourceFault resultEq => cases resultEq
  | committed trace heaps maps worlds frame metadata length continuation =>
    simp only [shift, List.range, List.range.loop, List.foldl, Expr.weakenAt, LanguageResult.success] at continuation
    cases continuation with
    | inRight continuation =>
      cases continuation
      exact ⟨_, _, _, _, trace, heaps, maps, worlds, frame, metadata⟩

/-- The seven-slot continuation is reflected by the universal expression IH,
not by an assumed runtime trace or closure-insensitive weakening rule. -/
example (program : SourceSemantics.Program) : ∃ outcome after finalMap finalWorld,
    DataPlaceContinuationReflection.Trace program sourceContext [] source sourceEnvironment heap place .equal id id outcome after ∧
    ResultRepresents model finalMap finalWorld .bool .bool faults outcome (.inRight .word (.bool true)) ∧
    GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
    GeneralHeap.LocationMap.Extends [0] finalMap ∧ WorldExtends world finalWorld ∧
    GeneralHeap.AdministrativePreserved [0] store finalMap finalStore ∧
    Dynamic.HeapMetadataExtend heap after := by
  have ranNext : runStateful 100 (.initial
      (execute prepared (.var 0) (SourceCoreCalls.packArguments []) code.expression code.expression .bool none false Word.zero)
      environment store) = .done (.inRight .word (.bool true)) finalStore := by cbv
  have assignment := DataPlaceAssignmentReflection.reflects (checked := checked) targetLayout
    (steps := []) (.nil rfl) (fuel := 5) (missing := fun _ => Word.zero) (.nil 0)
    (meaning program) functionTypes layouts observations faithful (fun _ => trivial)
    (Child.literal scope) found rfl rfl (Or.inl rfl) trivial (infer_sound (by decide))
    environments heapRelated locals rfl .head (.intro .head) rfl trivial
    (runStateful_evaluation_sound ranNext)
  exact DataPlaceContinuationReflection.reflects (meaning program) (Child.literal scope) found environments locals assignment

end Tests.SourceCoreDataPlaceAssignmentReflection

namespace Tests.SourceCoreDataPlaceAssignmentReflection.WordAbsent
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open SourceCoreDataPlaces DataPayload GenericExpressionMeaning

private def owner : Resolved.DeclarationId := ⟨⟨.main, ⟨[⟨"word_absent_reflection", by decide⟩], by decide⟩⟩, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "word_absent_reflection.solc"⟩, 0, 1⟩
private def five : Word := ⟨5, by decide⟩
private def invalid : Word := ⟨17, by decide⟩
private def binder : TypedBinder := ⟨⟨owner, 0⟩, "target", .mono .word, [], false, none⟩
private def id : ExpressionId := ⟨⟨owner, 0⟩⟩
private def node : ExpressionNode := { id, span, type := .word, form := .literal (.decimal "5") }
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
private def scope : Scope := [(binder.id, .word)]
private def place : PlaceResolution := ⟨binder.id, [], .word⟩
private def prepared : Prepared := ⟨⟨.word, .word, .word, [], none⟩, [], [], Word.zero⟩
private def code : SourceCoreBasic.LoweredExpr := ⟨.word, LanguageResult.success (.word five)⟩
private inductive Child : Certificate where
  | literal (scope : Scope) : Child scope id code
private def faults : FaultRep := fun reason token => match reason with
  | .invalidAssignmentOperands .add => token = invalid
  | .uninitializedLocation _ => token = Word.zero
  | .missingMappingDefault _ => token = Word.zero
  | _ => False
private theorem found : source.lookupExpression? id = some node := by cbv
private theorem literal : Literals.Tree source id (.word five) 1 :=
  .word (lookupExpression?_sound found) rfl rfl rfl rfl (interpretWordLiteral?_sound (by decide))
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
    exact ⟨.value (.word five), before, mapping, world,
      .value (literal.source_evaluates program sourceContext [] environment before), .value (.word five), heaps,
      .refl _, .refl _, .refl _ _, .refl _⟩

private theorem childLowered : SourceCoreBasic.lowerExpression 3 source scope id Word.zero = .ok code :=
  SourceCoreBasic.lowerExpression_word (node := node) (by cbv) rfl (by decide)
private def heap : Dynamic.Heap := ⟨[⟨.word, none, none⟩]⟩
private def store : Store := [.inLeft .word .unit, .integer 900]
private def world : StoreTyping := [OptionalCell.cellType .word, .integer]
private def sourceEnvironment : Dynamic.Environment := [(binder.id, ⟨0⟩)]
private def environment : Environment := [.cellRef (OptionalCell.cellType .word) 0]
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
private def next : Expr := LanguageResult.success (.storeCell (.var 0) (.inRight .unit (.word five)))
private def expression : Expr := execute prepared (.var 0) (SourceCoreCalls.packArguments []) code.expression
  next .unit (some .wordAdd) false invalid
example : lower checked signatures (fun fuel source scope id reasonAt =>
    SourceCoreBasic.lowerExpression fuel source scope id (reasonAt id)) 3 source scope (.occurrence id.occurrence)
    ⟨place, []⟩ .add (some id) .unit next (fun _ => Word.zero)
    Word.zero invalid (fun _ => Word.zero) = .ok expression := by
  have described : describe checked signatures source (.occurrence id.occurrence) ⟨place, []⟩ = .ok prepared.route := by cbv
  have preparedBy : prepare checked 3 prepared.route Word.zero (fun _ => Word.zero) = .ok prepared := by cbv
  have selected : SourceCoreLocalCell.lookup? scope place.root = some (0, Ty.word) := by cbv
  have rootEnsured : SourceCoreBasic.ensureType (.occurrence id.occurrence) prepared.route.rootType Ty.word = .ok () := by rfl
  simp only [lower, described, selected, rootEnsured, preparedBy, childLowered,
    bind, Except.bind, pure, Pure.pure, Except.pure]
  change (do
    let _ ← SourceCoreBasic.ensureType (.occurrence id.occurrence) Ty.word Ty.word
    pure (execute prepared (.var 0) (SourceCoreCalls.packArguments []) code.expression next .unit (some .wordAdd) false invalid)) = .ok expression
  rfl

example : infer? (SourceCoreLocalCell.coreContext scope) expression catalog.definitions =
    some (LanguageResult.resultType .unit) := by cbv
private def finalStore : Store := store
private theorem ran : runStateful 100 (.initial expression environment store) = .done (.inLeft .unit (.word invalid)) finalStore := by cbv

private theorem reflected (program : SourceSemantics.Program) :
    DataPlaceTailReflection.Result checked signatures functions program sourceContext [] source faults place .add id
      sourceEnvironment environment heap store [0] world next .unit
      (.inLeft .unit (.word invalid)) store := by
  exact DataPlaceAssignmentReflection.reflects (checked := checked) (operator := .add) (invalid := invalid) targetLayout
    (steps := []) (.nil rfl) (fuel := 5) (missing := fun _ => Word.zero) (.nil 0)
    (meaning program) functionTypes layouts observations faithful (fun _ => rfl)
    (Child.literal scope) found rfl rfl (Or.inr (Or.inl rfl)) rfl (infer_sound (by decide))
    environments heapRelated locals rfl .head (.intro .head) rfl rfl
    (runStateful_evaluation_sound ran)

/-- The exact modifier diagnostic is obtained from whole execution. The
continuation would initialize the source cell, but its write is suppressed. -/
example (program : SourceSemantics.Program) : ∃ reason token after finalMap finalWorld,
    Dynamic.SourcePlaceAssignmentFaults program sourceContext [] source sourceEnvironment heap place .add id reason after ∧
    faults reason token ∧ token = invalid ∧
    GenericHeap.HeapRepresents model finalMap finalWorld after store ∧
    GeneralHeap.AdministrativePreserved [0] store finalMap store := by
  cases reflected program with
  | fault trace resultEq tokenRep heaps maps worlds frame metadata =>
    have same := (Value.inLeft.inj resultEq).2
    have same := Value.word.inj same
    exact ⟨_, _, _, _, _, trace, tokenRep, same.symm, heaps, frame⟩
  | committed trace heaps maps worlds frame metadata length continuation =>
    simp only [shift, List.range, List.range.loop, List.foldl, Expr.weakenAt, next, LanguageResult.success] at continuation
    cases continuation

end Tests.SourceCoreDataPlaceAssignmentReflection.WordAbsent
