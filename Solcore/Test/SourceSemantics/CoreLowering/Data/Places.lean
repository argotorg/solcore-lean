import Solcore.SourceSemantics.CoreLowering.DataPlaceAssignmentSuccess
import Solcore.SourceSemantics.CoreLowering.Literals
import Solcore.SourceSemantics.CoreLowering.DataPlaceContinuationReflection
import Solcore.SourceSemantics.CoreLowering.DataPlaceGetterTyping
import Solcore.SourceSemantics.CoreLowering.DataPlaceCommitReflection
import Solcore.SourceSemantics.CoreLowering.DataPlaceContinuation
import Solcore.SourceSemantics.CoreLowering.DataPlaceGetterReflection
import Solcore.SourceSemantics.CoreLowering.DataPayloadCatalog
import Solcore.SourceSemantics.CoreLowering.DataPlaceKeyOrder
import Solcore.SourceSemantics.CoreLowering.BasicExpressionCertificates
import Solcore.SourceSemantics.CoreLowering.DataPlaceLayoutCertificates
import Solcore.SourceSemantics.CoreLowering.DataPlaceModifier
import Solcore.SourceSemantics.CoreLowering.DataPlaceModifierReflection
import Solcore.SourceSemantics.CoreLowering.DataPlacePrefixReflection
import Solcore.SourceSemantics.CoreLowering.DataPlaceMemberCertificates
import Solcore.SourceSemantics.CoreLowering.DataPlaceReadReflection
import Solcore.SourceSemantics.CoreLowering.DataPlaceMappingHelpers
import Solcore.SourceSemantics.CoreLowering.DataMappingHeap
import Solcore.SourceSemantics.CoreLowering.DataPlaceFaultTree
import Solcore.SourceSemantics.CoreLowering.DataPlacePathHelpers
import Solcore.SourceSemantics.CoreLowering.DataPlaceRhsReflection
import Solcore.SourceSemantics.CoreLowering.DataPlaceSetterReflection
import Solcore.SourceSemantics.CoreLowering.DataPlaceWriteBack
import Solcore.SourceSemantics.CoreLowering.DataPlaceExecution
import Solcore.Frontend.SourceCoreGeneralFunctions

/-!
# Data place tests

Data places: paths, reads, writes, keys, modifiers and reflection.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreDataPlaceAssignmentMeaning
/-! A complete source/Core assignment proof consumer uses an actual accepted
place and expression compiler, an absent ordinary source cell, two Core aliases
and an unmapped administrative cell. Separate generated-code checks observe
snapshot-before-RHS and latest-root reconstruction of an untouched member.
-/
set_option autoImplicit false
set_option maxRecDepth 4096
namespace Tests.SourceCoreDataPlaceAssignmentMeaning
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open SourceCoreDataPlaces GeneralHeap GenericExpressionMeaning DataPayload

private def owner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"assignment_meaning", by decide⟩], by decide⟩⟩, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "assignment_meaning.solc"⟩, 0, 1⟩
private def binder : TypedBinder := ⟨⟨owner, 0⟩, "root", .mono .bool, [], false, none⟩
private def rhs : ExpressionId := ⟨⟨owner, 0⟩⟩
private def node : ExpressionNode := {id := rhs, span, type := .bool, form := .reference "true" (.builtinBoolean true)}
private def source : TypedSource := {owner, inputs := [binder], roots := [.expression rhs], nodes := [.expression node]}
private def catalog : SourceCoreDataCatalog.Catalog := {}
private def checked : SourceCoreDataCatalog.Checked := ⟨catalog, DataEnvironment.isWellFormed_sound (by decide)⟩
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def functions : GenericHeap.PayloadModel catalog where
  Represents := fun _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  extend := fun impossible _ _ => False.elim impossible
private def model := payloadModel catalog signatures functions
private def context := (SourceSemantics.Context.ofSignatures signatures).withLocal binder.id binder.scheme
private def code : SourceCoreBasic.LoweredExpr := ⟨.bool, LanguageResult.success (.bool true)⟩
private def scope : Scope := [(binder.id, .bool)]
private def assignment : AssignmentResolution := ⟨⟨binder.id, [], .bool⟩, []⟩
private def route : Route := ⟨.bool, .bool, .bool, [], none⟩
private def prepared : Prepared := ⟨route, [], [], Word.zero⟩
private def site : SourceCoreElaboration.ErrorSite := .occurrence rhs.occurrence

example : describe checked signatures source site assignment = .ok route := by cbv
example : prepare checked 10 route Word.zero (fun _ => Word.zero) = .ok prepared := by cbv
example : SourceCoreBasic.lowerExpression 4 source scope rhs Word.zero = .ok code := by cbv

private inductive Child : Certificate where
  | literal (scope : Scope) : Child scope rhs code
private theorem found : source.lookupExpression? rhs = some node := by cbv
private theorem unique : NodeOccurrencesUnique source := by
  simp [NodeOccurrencesUnique, nodeOccurrenceIds, source, node, Node.occurrenceId, Node.id, NodeId.occurrenceId, rhs]
private theorem literal : Literals.Tree source rhs (.bool true) 1 :=
  .bool (lookupExpression?_sound found) rfl rfl rfl rfl

private theorem no_fault {program : SourceSemantics.Program} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    (failed : Dynamic.ExpressionFaults program context [] source environment before rhs reason after) : False := by
  have sameNode {selected : ExpressionNode} (contained : ContainsExpression source rhs selected) : selected = node :=
    Option.some.inj ((lookupExpression?_complete unique contained).symm.trans found)
  cases failed with
  | missing absent => exact Dynamic.ExpressionAbsentIn.excludes_contains absent (lookupExpression?_sound found)
  | form contained failed => have same := sameNode contained; subst_vars; cases failed
  | coercion contained _ failed => have same := sameNode contained; subst_vars; cases failed
  | generalizedLocalRequirement contained other _ _ _ _ _ _ _ =>
    have same := sameNode contained; subst_vars; cases other
  | generalizedLocalCoercion contained other _ _ _ _ _ _ _ =>
    have same := sameNode contained; subst_vars; cases other

private theorem meaning (program : SourceSemantics.Program) :
    Preserves model program context [] source Child (fun _ _ => False) := by
  intro localScope expression lowered certified selected selectedBy mapping world admin environment canonical actual
    before store ξ outcome after environments heaps locals layout evaluated
  cases certified
  have same := Option.some.inj (selectedBy.symm.trans found)
  subst selected
  cases evaluated with
  | value evaluated =>
    obtain ⟨rfl, rfl⟩ := literal.source_sound unique evaluated
    exact ⟨_, store, mapping, world, .inRight .bool, .value (.bool true), heaps,
      .refl _, .refl _, .refl _ _, .refl _⟩
  | fault failed => exact (no_fault failed).elim

private theorem observations : FunctionObservations catalog signatures functions (fun _ _ => False) :=
  fun impossible => False.elim impossible
private theorem faithful : DataEquality.IdentityFaithful (fun _ _ => False) := by
  constructor <;> intros <;> contradiction
private theorem layouts : CatalogLayouts catalog := by constructor <;> intros <;> contradiction
private def referenceType : Ty := OptionalCell.referenceType .bool
private def before : Dynamic.Heap := ⟨[⟨.bool, none, none⟩]⟩
private def after : Dynamic.Heap := ⟨[⟨.bool, some (.bool true), none⟩]⟩
private def world : StoreTyping := [OptionalCell.cellType .bool, .integer]
private def store : Store := [.inLeft .bool .unit, .integer 900]
private def sourceEnvironment : Dynamic.Environment := [(binder.id, ⟨0⟩)]
private def coreEnvironment : Environment := [.cellRef (OptionalCell.cellType .bool) 0, .cellRef (OptionalCell.cellType .bool) 0]
private def target : Dynamic.ResolvedPlace := ⟨⟨0⟩, .bool, .bool, [], none⟩
private def expression : Expr := execute prepared (.var 0) (SourceCoreCalls.packArguments []) code.expression
  (LanguageResult.success .unit) .unit none false Word.zero

private theorem heapRelated : GenericHeap.HeapRepresents model [0] world before store := by
  have empty : GenericHeap.HeapRepresents model [] [] ⟨[]⟩ [] := .empty
  exact (empty.allocate (.uninitialized rfl) .append).1.allocate_administrative .integer
private theorem environments : DataHeap.EnvRepresents catalog [0] world [referenceType] scope sourceEnvironment coreEnvironment :=
  .cons ⟨rfl, rfl⟩ (.nil (.cons (.cellRef rfl) .nil))
private theorem locals : Dynamic.EnvironmentAgrees before context.locals sourceEnvironment :=
  .cons (.intro .head) rfl (.ordinary rfl rfl) .nil
private theorem targetLayout : DataPlaceResolvedTarget.Layout checked signatures functions source Child scope assignment.target
    prepared [] [] (SourceCoreLocalCell.coreContext scope ++ [referenceType]) := by
  refine ⟨.nil, rfl, .ordinary (by intro impossible; rcases impossible with ⟨_, _, same⟩; cases same) rfl, ?_, ?_⟩
  · intro mapping world sources values projections shaped represented
    cases shaped
    exact ⟨0, .nil rfl⟩
  · exact infer_sound (by decide)

private theorem resolved (program : SourceSemantics.Program) :
    Dynamic.SourcePlaceResolves program context [] source sourceEnvironment before assignment.target target before :=
  .intro (before := before) (after := before) (place := assignment.target) (location := ⟨0⟩)
    (initialCell := ⟨.bool, none, none⟩) (currentCell := ⟨.bool, none, none⟩)
    .head (.intro .head) .nil (.intro .head)
    (.uninitialized (type := .bool) (by intro impossible; rcases impossible with ⟨_, _, same⟩; cases same)) .nil
private theorem not_mapping : ¬ ∃ key value, (.bool : TypeSystem.Ty) = .mapping key value := by
  intro impossible; rcases impossible with ⟨_, _, same⟩; cases same

private theorem written : Dynamic.ResolvedPlaceWrites (fun _ updated => Dynamic.AssignmentValueApplies .equal none (.bool true) updated)
    before target (.bool true) after :=
  .intro (.intro .head) rfl (.uninitialized (type := .bool) not_mapping)
    (.leaf (.equal _ _)) (.intro (.intro .head) .head)

private theorem complete (program : SourceSemantics.Program) : ∃ updatedValue finalStore finalMap finalWorld,
    Dynamic.SourcePlaceAssignment program context [] source (Dynamic.AssignmentValueApplies .equal)
      sourceEnvironment before assignment.target rhs (.bool true) after ∧
    Evaluates coreEnvironment store expression (.inRight .word .unit) finalStore ∧
    ValueRep catalog signatures functions finalMap finalWorld .bool (.bool true) updatedValue .bool ∧
    GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
    LocationMap.Extends [0] finalMap ∧ WorldExtends world finalWorld ∧
    AdministrativePreserved [0] store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  exact DataPlaceAssignmentSuccess.preserves targetLayout (meaning program) observations faithful layouts
    (Child.literal scope) found rfl rfl (.inl rfl) (infer_sound (by decide)) environments heapRelated locals
    rfl rfl (resolved program) (literal.source_evaluates program context [] sourceEnvironment before) written Word.zero

example (program : SourceSemantics.Program) : ∃ finalStore finalMap finalWorld required,
    (∀ fuel, required ≤ fuel → runStateful fuel (.initial expression coreEnvironment store) =
      .done (.inRight .word .unit) finalStore) ∧
    GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
    AdministrativePreserved [0] store finalMap finalStore := by
  obtain ⟨_, finalStore, finalMap, finalWorld, _, evaluated, _, heaps, _, _, frame, _⟩ := complete program
  obtain ⟨required, runs⟩ := evaluation_runStateful_complete_with_sufficient_fuel evaluated
  exact ⟨finalStore, finalMap, finalWorld, required, runs, heaps, frame⟩

example : lower checked signatures (fun fuel source scope id reasonAt => SourceCoreBasic.lowerExpression fuel source scope id (reasonAt id)) 4 source scope site assignment .equal (some rhs)
    .unit (LanguageResult.success .unit) (fun _ => Word.zero) Word.zero Word.zero (fun _ => Word.zero) = .ok expression := by cbv
example : infer? [referenceType, referenceType] expression = some (LanguageResult.resultType .unit) := by cbv
example : runStateful 100 (.initial expression coreEnvironment store) =
    .done (.inRight .word .unit) [.inRight .unit (.bool true), .integer 900] := by cbv

private def observeAliases : Expr := .letE expression
  (LanguageResult.success (.pair (.loadCell (.var 1)) (.loadCell (.var 2))))
example : runStateful 120 (.initial observeAliases coreEnvironment store) =
    .done (.inRight .word (.pair (.inRight .unit (.bool true)) (.inRight .unit (.bool true))))
      [.inRight .unit (.bool true), .integer 900] := by cbv

/-- Compound assignment uses the old first field but reconstructs the latest
second field written by the RHS. These are the actual production helpers. -/
private def tag : ConstructorId := ⟨⟨0⟩, 0⟩
private def memberPrepared : Prepared :=
  ⟨⟨.unit, .namedData ⟨0⟩, .integer, [], none⟩,
    [.member ⟨0⟩ 0 [⟨tag, [.integer, .integer]⟩] .integer], [], Word.zero⟩
private def memberRhs : Expr := .letE
  (.storeCell (.var 0) (.inRight .unit (.construct tag (.pair (.integer 100) (.integer 22)))))
  (LanguageResult.success (.integer 5))
private def memberCode : Expr := execute memberPrepared (.var 0) (SourceCoreCalls.packArguments []) memberRhs
  (LanguageResult.success .unit) .unit (some .integerAdd) false Word.zero
example : infer? [.cell (.sum .unit (.namedData ⟨0⟩))] memberCode [⟨[.product .integer .integer]⟩] =
    some (LanguageResult.resultType .unit) := by cbv
example : runStateful 200 (.initial memberCode [.cellRef (.sum .unit (.namedData ⟨0⟩)) 0]
    [.inRight .unit (.constructed tag (.pair (.integer 7) (.integer 11)))]) =
    .done (.inRight .word .unit) [.inRight .unit (.constructed tag (.pair (.integer 12) (.integer 22)))] := by cbv

private def mappingLayout : Core.OrderedMapping.Layout := ⟨.bool, .bool, ⟨0⟩⟩
private def mappingCatalog : SourceCoreDataCatalog.Catalog := {
  entries := [{sourceType := .mapping .bool .bool, definition := some mappingLayout.definition}] }
private def mappingFunctions : GenericHeap.PayloadModel mappingCatalog where
  Represents := fun _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  extend := fun impossible _ _ => False.elim impossible
private def mappingPrepared : Prepared :=
  ⟨⟨.mapping .bool .bool, mappingLayout.type, mappingLayout.type, [], some mappingLayout⟩, [], [], Word.zero⟩

/-- Virtual empty mapping construction authenticates its metadata and leaves
the uninitialized source cell unwritten until an assignment commits. -/
example : ∃ value,
    DataPlacePathHelpers.Root mappingPrepared ⟨.mapping .bool .bool, none, none⟩
      (.inLeft mappingLayout.type .unit) (.mapping .bool .bool []) value ∧
    ValueRep mappingCatalog signatures mappingFunctions [] [] (.mapping .bool .bool)
      (.mapping .bool .bool []) value mappingLayout.type := by
  apply DataPlaceSnapshot.root_present
  · exact .mapping rfl (by decide) rfl rfl ⟨.bool, .bool, rfl⟩
  · exact .uninitialized (by cbv)
  · exact .emptyMapping .bool .bool

private def mappingSnapshot : Expr := .apply (getter mappingPrepared .unit) (.pair (.loadCell (.var 0)) .unit)
example : runStateful 50 (.initial mappingSnapshot [.cellRef (.sum .unit mappingLayout.type) 0]
    [.inLeft mappingLayout.type .unit]) =
    .done (.inRight .word (.inRight .unit (Core.OrderedMapping.encode mappingLayout [])))
      [.inLeft mappingLayout.type .unit] := by cbv

end Tests.SourceCoreDataPlaceAssignmentMeaning
end

section
-- leanmerge: from Solcore.Test.SourceCoreDataPlaceAssignmentReflection
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
end

section
-- leanmerge: from Solcore.Test.SourceCoreDataPlaceCatalogBoundary
/-! Finite well-formed Core definitions do not authenticate nominal catalog
row completeness. The real entry checker must retain that separate boundary. -/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace Tests.SourceCoreDataPlaceCatalogBoundary
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open SourceCoreDataPlaces

private def moduleId : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"place_catalog", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def dataId : Resolved.DeclarationId := ⟨moduleId, 1⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "place_catalog.solc"⟩, 0, 1⟩
private def site : SourceCoreElaboration.ErrorSite := .occurrence ⟨owner, 0⟩
private def boxType : TypeSystem.Ty := .nominal dataId []
private def signature : ProgramDataSignature := {
  id := dataId, name := "Box", parameters := []
  constructors := [⟨⟨dataId, 0⟩, "Box", [.integer], ⟨span, ⟨[], ⟨span, "Box"⟩, none⟩⟩⟩]
  source := ⟨span, ⟨none, ⟨span, "Box"⟩, none, span, []⟩⟩ }
private def signatures : ProgramSignatures := ⟨[], [], [], [], [signature], []⟩
private def catalog : SourceCoreDataCatalog.Catalog := { entries := [
  { sourceType := boxType, definition := some ⟨[.integer, .integer]⟩, constructors := [⟨dataId, 0⟩] }] }
private def checked : SourceCoreDataCatalog.Checked :=
  ⟨catalog, Core.DataEnvironment.isWellFormed_sound (by decide)⟩
private def binder : TypedBinder := ⟨⟨owner, 0⟩, "root", .mono boxType, [], false, none⟩
private def source : TypedSource := { owner, inputs := [binder], roots := [], nodes := [] }
private def assignment : AssignmentResolution := ⟨⟨binder.id, [.member "field" 0], .integer⟩, []⟩
private def route : Route := ⟨boxType, .namedData ⟨0⟩, .integer,
  [.member ⟨0⟩ 0 [⟨⟨⟨0⟩, 0⟩, [.integer]⟩] .integer], none⟩
private def prepared : Prepared := ⟨route, [.member ⟨0⟩ 0 [⟨⟨⟨0⟩, 0⟩, [.integer]⟩] .integer], [], Word.zero⟩

example : describe checked signatures source site assignment = .ok route := by cbv
example : prepare checked 20 route Word.zero (fun _ => Word.zero) = .ok prepared := by cbv

/-- The compiler produced one branch from the one genuine source constructor,
while the merely finite-well-formed catalog declares two Core alternatives. -/
example : infer? [] (getter prepared .unit) catalog.definitions = none := by cbv

/-- This is rejected statically; it is not a source-program runtime fault. -/
example : ¬ ∃ type, HasType [] (getter prepared .unit) type catalog.definitions := by
  rintro ⟨type, typed⟩
  have inferred := infer_complete typed
  have absent : infer? [] (getter prepared .unit) catalog.definitions = none := by cbv
  rw [absent] at inferred
  cases inferred

end Tests.SourceCoreDataPlaceCatalogBoundary
end

section
-- leanmerge: from Solcore.Test.SourceCoreDataPlaceCommitReflection
/-! The actual final storeCell updates a mapped source cell between administrative
cells. Two runtime aliases observe that same update, while source metadata and
both administrative sentinels remain unchanged. -/
set_option autoImplicit false
namespace Tests.SourceCoreDataPlaceCommitReflection
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open GeneralHeap DataPayload

private def catalog : SourceCoreDataCatalog.Catalog := {}
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def functions : GenericHeap.PayloadModel catalog where
  Represents := fun _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  extend := fun impossible _ _ => False.elim impossible
private def model := payloadModel catalog signatures functions
private def cell : Dynamic.Cell := ⟨.bool, some (.bool false), none⟩
private def heap : Dynamic.Heap := ⟨[cell]⟩
private def finalHeap : Dynamic.Heap := ⟨[{cell with value := some (.bool true)}]⟩
private def world : StoreTyping := [.integer, OptionalCell.cellType .bool, .integer]
private def store : Store := [.integer 900, .inRight .unit (.bool false), .integer 901]
private def finalStore : Store := [.integer 900, .inRight .unit (.bool true), .integer 901]
private def reference : Value := .cellRef (OptionalCell.cellType .bool) 1
private def environment : Environment := [reference, .bool true, reference]
private def expression : Expr := .storeCell (.var 0) (.inRight .unit (.var 1))
private theorem heapRelated : GenericHeap.HeapRepresents model [1] world heap store := by
  have empty : GenericHeap.HeapRepresents model [] [] ⟨[]⟩ [] := .empty
  have withPrefix := empty.allocate_administrative (value := .integer 900) .integer
  exact (withPrefix.allocate (.initialized (.bool false)) .append).1.allocate_administrative .integer
private theorem ran : runStateful 30 (.initial expression environment store) = .done .unit finalStore := by cbv

example : ∃ after,
    Dynamic.Heap.Writes heap ⟨0⟩ (some (.bool true)) after ∧
    GenericHeap.HeapRepresents model [1] world after finalStore ∧
    AdministrativePreserved [1] store [1] finalStore ∧
    Dynamic.HeapMetadataExtend heap after ∧
    finalStore.read? 1 = some (.inRight .unit (.bool true)) := by
  obtain ⟨after, _, written, heaps, frame, metadata, observed⟩ :=
    DataPlaceCommitReflection.reflects_storeCell heapRelated
      (show ReferenceRepresents [1] world ⟨0⟩ 1 .bool from ⟨rfl, rfl⟩)
      (.intro .head) (show model.Represents [1] world .bool (.bool true) (.bool true) .bool from .bool true)
      (.var rfl) (.var rfl) (runStateful_evaluation_sound ran)
  exact ⟨after, written, heaps, frame, metadata, observed⟩

/-- Allocation metadata remains exactly the source declaration's metadata. -/
example : Dynamic.Heap.Writes heap ⟨0⟩ (some (.bool true)) finalHeap :=
  DataPlaceCommitReflection.source_writes (.intro .head) _

/-- Both aliases see the update; they are not copies of the previous payload. -/
example : runStateful 50 (.initial
    (.letE expression (.pair (.loadCell (.var 1)) (.loadCell (.var 3)))) environment store) =
      .done (.pair (.inRight .unit (.bool true)) (.inRight .unit (.bool true))) finalStore := by cbv

/-- Reinterpreting a reconstructed root with an authenticated modifier keeps
the first duplicate's position and the remaining entries unchanged. -/
example : Dynamic.ProjectionsUpdate
    (fun _ value => Dynamic.AssignmentValueApplies .equal (some (.bool false)) (.bool true) value)
    (some (.mapping .bool .bool [(.bool true, .bool false), (.bool true, .bool false)]))
    [.index (.bool true)]
    (.mapping .bool .bool [(.bool true, .bool true), (.bool true, .bool false)]) := by
  apply DataPlaceCommitReflection.update_of_replacement
    (replacement := .bool true)
  · exact .indexFound (.head ⟨rfl, .bool true⟩) (.leaf rfl) (.update (.head ⟨rfl, .bool true⟩))
  · intro snapshot
    exact .equal _ _

end Tests.SourceCoreDataPlaceCommitReflection
end

section
-- leanmerge: from Solcore.Test.SourceCoreDataPlaceContinuation
/-! The continuation law retains the actual seven-slot capture environment.
Returning and invoking a closure observes the completed assignment; a failing
continuation also retains the already committed store.
-/
set_option autoImplicit false
namespace Tests.SourceCoreDataPlaceContinuation
open Solcore Solcore.Core Solcore.Frontend Solcore.SourceSemantics.CoreLowering
open SourceCoreDataPlaces DataPlaceContinuation

private def prepared : Prepared := ⟨⟨.integer, .integer, .integer, [], none⟩, [], [], Word.zero⟩
private def environment : Environment := [.cellRef (.sum .unit .integer) 0]
private def before : Store := [.inRight .unit (.integer 3), .integer 900]
private def after : Store := [.inRight .unit (.integer 17), .integer 900]
private def rhs : Expr := LanguageResult.success (.integer 17)
private def terminal : Expr := execute prepared (.var 0) (SourceCoreCalls.packArguments []) rhs
  (LanguageResult.success .unit) .unit none false Word.zero
private theorem completed : Evaluates environment before terminal (.inRight .word .unit) after :=
  runStateful_evaluation_sound (show runStateful 100 (.initial terminal environment before) =
    .done (.inRight .word .unit) after by cbv)

private def closureType : Ty := .function .unit (.sum .unit .integer)
private def next : Expr := LanguageResult.success (.lambda .unit (.sum .unit .integer) (.loadCell (.var 1)))
private def captures : Expr := execute prepared (.var 0) (SourceCoreCalls.packArguments []) rhs
  next closureType none false Word.zero

/-- The law does not equate closures that capture different environments.
It explicitly retains the seven values actually introduced by execute. -/
example : ∃ slots : Environment, slots.length = 7 ∧
    Evaluates environment before captures
      (.inRight .word (.closure .unit (.sum .unit .integer) (.loadCell (.var 8)) (slots ++ environment))) after := by
  obtain ⟨slots, length, finish⟩ := plug completed
  refine ⟨slots, length, finish ?_⟩
  simp [next, shift, List.range, List.range.loop, List.foldl, LanguageResult.success, Expr.weakenAt]
  exact .inRight .lambda

private def invoke : Expr := LanguageResult.bind (.sum .unit .integer) captures
  (LanguageResult.success (.apply (.var 0) .unit))
example : infer? [.cell (.sum .unit .integer)] invoke = some (.sum .word (.sum .unit .integer)) := by cbv
example : runStateful 140 (.initial invoke environment before) =
    .done (.inRight .word (.inRight .unit (.integer 17))) after := by cbv

private def failing : Expr := execute prepared (.var 0) (SourceCoreCalls.packArguments []) rhs
  (LanguageResult.failure .bool (.word Word.zero)) .bool none false Word.zero
example : Evaluates environment before failing (.inLeft .bool (.word Word.zero)) after := by
  obtain ⟨slots, _, finish⟩ := plug completed
  apply finish
  simp only [shift, List.range, List.range.loop, List.foldl, LanguageResult.failure, Expr.weakenAt]
  exact .inLeft .word
example : runStateful 100 (.initial failing environment before) = .done (.inLeft .bool (.word Word.zero)) after := by cbv

/-- Source finite evaluation can be fed through the universal continuation
theorem in the production compiler proof; no additional fuel contract is
needed for this algebraic phase. -/
example : ∃ required, ∀ fuel, required ≤ fuel →
    runStateful fuel (.initial terminal environment before) = .done (.inRight .word .unit) after :=
  evaluation_runStateful_complete_with_sufficient_fuel completed

end Tests.SourceCoreDataPlaceContinuation
end

section
-- leanmerge: from Solcore.Test.SourceCoreDataPlaceExactFault
/-! An outer missing mapping defaults to an empty inner mapping. The actual
selector and updater must report the inner unavailable-function default token,
without running an arbitrary replacement or rewriting the store prefix. -/
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000
set_option cbv.maxSteps 2500000
namespace Tests.SourceCoreDataPlaceExactFault
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open SourceCoreDataPlaces DataPayload DataPlaceRouteCertificates

private def signatures : ProgramSignatures := { functions := [], implRules := [], traits := [], implementations := [] }
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"exact_fault", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "exact_fault.solc"⟩, 0, 1⟩
private def first : ExpressionId := ⟨⟨owner, 0⟩⟩
private def second : ExpressionId := ⟨⟨owner, 1⟩⟩
private def firstNode : ExpressionNode := { id := first, span, type := .bool, form := .reference "true" (.builtinBoolean true) }
private def secondNode : ExpressionNode := { id := second, span, type := .bool, form := .reference "false" (.builtinBoolean false) }
private def functionType : TypeSystem.Ty := .function .unit .unit
private def innerType : TypeSystem.Ty := .mapping .bool functionType
private def rootType : TypeSystem.Ty := .mapping .bool innerType
private def inner : Core.OrderedMapping.Layout := ⟨.bool, TaggedFunction.functionType .unit .unit, ⟨0⟩⟩
private def outer : Core.OrderedMapping.Layout := ⟨.bool, inner.type, ⟨1⟩⟩
private def catalog : SourceCoreDataCatalog.Catalog := { entries := [
  { sourceType := innerType, definition := some inner.definition },
  { sourceType := rootType, definition := some outer.definition }] }
private def checked : SourceCoreDataCatalog.Checked := ⟨catalog, DataEnvironment.isWellFormed_sound (by decide)⟩
private def source : TypedSource := { owner, inputs := [], roots := [.expression first, .expression second], nodes := [.expression firstNode, .expression secondNode] }
private def projections : List PlaceProjection := [.index first, .index second]
private def route : Route := ⟨rootType, outer.type, inner.valueType,
  [.index outer first innerType, .index inner second functionType], some outer⟩
private def missing (type : TypeSystem.Ty) : Word := if type = functionType then ⟨31, by decide⟩ else ⟨17, by decide⟩
private theorem existsPrepared : (prepare checked 15 route Word.zero missing).toOption.isSome = true := by cbv
private def prepared : Prepared := (prepare checked 15 route Word.zero missing).toOption.get existsPrepared
private theorem except_get {α ε : Type} (result : Except ε α) (positive : result.toOption.isSome = true) :
    result = .ok (result.toOption.get positive) := by
  cases result with
  | error => simp [Except.toOption] at positive
  | ok => rfl
private theorem preparedBy : prepare checked 15 route Word.zero missing = .ok prepared := except_get _ existsPrepared
private def functions : GenericHeap.PayloadModel catalog where
  Represents := fun _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  extend := fun impossible _ _ => False.elim impossible
private theorem observations : FunctionObservations catalog signatures functions (fun _ _ => False) := fun impossible => False.elim impossible
private theorem faithful : DataEquality.IdentityFaithful (fun _ _ => False) := by constructor <;> intros <;> contradiction
private theorem innerRegistered : inner.Registered catalog.definitions :=
  ⟨.bool, .product (.sum .unit .word) (.function .unit (.sum .word .unit)), rfl⟩
private theorem outerRegistered : outer.Registered catalog.definitions := ⟨.bool, .namedData rfl, rfl⟩
private theorem layouts : CatalogLayouts catalog := by
  apply CatalogLayouts.of_entries
  intro id entry selected
  rcases id with ⟨index⟩
  cases index with
  | zero => cases selected; exact ⟨.bool, inner.valueType, rfl, rfl, innerRegistered⟩
  | succ index => cases index with
    | zero => cases selected; exact ⟨.bool, inner.type, rfl, rfl, outerRegistered⟩
    | succ index => simp [catalog] at selected
private theorem raw : RawPath checked signatures source rootType outer.type route.steps projections functionType inner.valueType [.bool, .bool] :=
  .index (layout := outer) rfl rfl rfl rfl (show source.lookupExpression? first = some firstNode by cbv) rfl
    (.index (layout := inner) rfl rfl rfl rfl (show source.lookupExpression? second = some secondNode by cbv) rfl (.nil rfl))
private theorem shaped : DataPlaceKeyOrder.Values projections [.bool true, .bool false] [.index (.bool true), .index (.bool false)] :=
  .index (.index .nil)
private theorem keyValues {mapping : GeneralHeap.LocationMap} {world : StoreTyping} : DataExpressionSequence.Values (payloadModel catalog signatures functions) mapping world [.bool, .bool]
    [.bool, .bool] [.bool true, .bool false] [.bool true, .bool false] := .cons (.bool true) (.cons (.bool false) .nil)
private def sourceRoot : Dynamic.Value := .mapping .bool innerType []
private def coreRoot : Value := .constructed outer.nilConstructor .unit
private theorem related : ValueRep catalog signatures functions [] [] rootType sourceRoot coreRoot outer.type :=
  .mapping rfl rfl rfl outerRegistered (.empty _ _ _ _)
private theorem sourceFault : Dynamic.ProjectionsFaults (some sourceRoot) [.index (.bool true), .index (.bool false)]
    (.missingMappingDefault functionType) := by
  exact .indexDefault (.bool true) .nil (.mapping _ _)
    (.indexDefaultUnavailable (.bool false) .nil (by intro impossible; cases impossible))

example (environment : Environment) (store : Store) (replacement : Expr) :
    ∃ after administrative,
      Evaluates (coreRoot :: .pair (.bool true) (.bool false) :: environment) store
        (select prepared prepared.steps (.var 0) (.var 1))
        (.inLeft prepared.optionalLeaf (.word ⟨31, by decide⟩)) after ∧
      Evaluates (coreRoot :: .pair (.bool true) (.bool false) :: environment) store
        (update prepared prepared.steps outer.type (.var 0) (.var 1) replacement)
        (.inLeft outer.type (.word ⟨31, by decide⟩)) after ∧ after = store ++ administrative := by
  simpa only [DataPlaceExactFault.token, missing, ↓reduceIte] using
    DataPlaceExactFault.preserves observations faithful layouts raw
      (DataPlaceMappingPreparation.steps_of_prepare preparedBy).2.2 shaped (keyValues (mapping := []) (world := []))
      (allKeys := [.bool true, .bool false]) (by intro i v selected; simpa using selected) (by cbv)
      related sourceFault (coreRoot :: .pair (.bool true) (.bool false) :: environment) store
      (.var 0) (.var 1) replacement (DataEquality.Selects.var rfl) (DataEquality.Selects.var (index := 1) rfl)

example : missing innerType ≠ missing functionType := by decide

private def model := payloadModel catalog signatures functions
private def cell : Dynamic.Cell := ⟨rootType, none, none⟩
private def heap : Dynamic.Heap := ⟨[cell]⟩
private def world : StoreTyping := [OptionalCell.cellType outer.type, .integer]
private def before : Store := [.inLeft outer.type .unit, .integer 900]
private def environment : Environment := [.cellRef (OptionalCell.cellType outer.type) 0, .pair (.bool true) (.bool false)]
private def expression : Expr := .apply (getter prepared (.product .bool .bool))
  (.pair (.loadCell (.var 0)) (.var 1))
private theorem heapRelated : GenericHeap.HeapRepresents model [0] world heap before := by
  have empty : GenericHeap.HeapRepresents model [] [] ⟨[]⟩ [] := .empty
  exact (empty.allocate (.uninitialized rfl) .append).1.allocate_administrative .integer
private theorem functionTypes : FunctionRuntimeTypes functions := fun impossible => False.elim impossible
private theorem preparedRoute : prepared.route = route := (DataPlaceMappingPreparation.steps_of_prepare preparedBy).1
private theorem rawPrepared : RawPath checked signatures source rootType prepared.route.rootType route.steps projections functionType prepared.route.leafType [.bool, .bool] := by
  rw [preparedRoute]
  exact raw
private theorem rootLayout : DataPlaceSnapshot.RootLayout catalog prepared rootType :=
  .mapping (by rw [preparedRoute]; rfl) rfl rfl rfl outerRegistered
private def summary : StatefulRunResult → Option (Value × Nat × Store)
  | .done value store => some (value, store.length, store.take 2)
  | _ => none
private theorem actualRun : summary (runStateful 1000 (.initial expression environment before)) =
    some (.inLeft prepared.optionalLeaf (.word ⟨31, by decide⟩), 8, before) := by cbv

/-- The root remains uninitialized: both outer/inner mappings are virtual,
while the two lookup invocations append six ordinary helper cells. Reflection
constructs the independent source failure without an assumed source trace. -/
example : ∃ result after futureWorld administrative,
    runStateful 1000 (.initial expression environment before) = .done result after ∧
    result = .inLeft prepared.optionalLeaf (.word ⟨31, by decide⟩) ∧ after.length = 8 ∧
    DataPlaceGetterReflection.ResultRep catalog signatures functions [0] futureWorld prepared missing
      functionType cell [.index (.bool true), .index (.bool false)] result ∧
    GenericHeap.HeapRepresents model [0] futureWorld heap after ∧
    GeneralHeap.AdministrativePreserved [0] before [0] after ∧ after = before ++ administrative := by
  have measured := actualRun
  cases ran : runStateful 1000 (.initial expression environment before) with
  | outOfFuel => simp [ran, summary] at measured
  | fault => simp [ran, summary] at measured
  | done result after =>
    simp only [ran, summary, Option.some.injEq, Prod.mk.injEq] at measured
    obtain ⟨futureWorld, administrative, represented, _, heaps, _, frame, appended⟩ :=
      DataPlaceGetterReflection.reflects_at functionTypes layouts observations faithful (cell := cell) rawPrepared
        (DataPlaceMappingPreparation.steps_of_prepare preparedBy).2.2 shaped keyValues (by cbv) rootLayout
        heapRelated (by rw [preparedRoute]; exact ⟨rfl, rfl⟩) (.intro .head)
        (show RuntimeEnvironmentHasTypes world environment [OptionalCell.referenceType outer.type, .product .bool .bool] catalog.definitions from
          .cons (.cellRef rfl) (.cons (.pair .bool .bool) .nil))
        (infer_sound (show infer? [OptionalCell.referenceType outer.type, .product .bool .bool] expression catalog.definitions =
          some (LanguageResult.resultType prepared.optionalLeaf) by cbv))
        (by rw [preparedRoute]; exact .var rfl) (.var (index := 1) rfl) (runStateful_evaluation_sound ran)
    exact ⟨result, after, futureWorld, administrative, rfl, measured.1, measured.2.1, represented, heaps, frame, appended⟩

end Tests.SourceCoreDataPlaceExactFault
end

section
-- leanmerge: from Solcore.Test.SourceCoreDataPlaceGetterReflection
/-! A live ordinary absent cell is accepted as the snapshot of a bare place,
but a named member projection reports the invalid-projection token. Both are
actual checked helpers and finite Core runs; reflection supplies the independent
root/read outcome without requiring a source trace. -/
set_option autoImplicit false
set_option maxRecDepth 16384
namespace Tests.SourceCoreDataPlaceGetterReflection
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open SourceCoreDataPlaces DataPayload DataPlaceRouteCertificates

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"getter_reflection", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def dataId : Resolved.DeclarationId := ⟨moduleId, 1⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "getter_reflection.solc"⟩, 0, 1⟩
private def boxType : TypeSystem.Ty := .nominal dataId []
private def signature : ProgramDataSignature := {
  id := dataId, name := "Box", parameters := []
  constructors := [⟨⟨dataId, 0⟩, "Box", [.bool], ⟨span, ⟨[], ⟨span, "Box"⟩, none⟩⟩⟩]
  source := ⟨span, ⟨none, ⟨span, "Box"⟩, none, span, []⟩⟩ }
private def signatures : ProgramSignatures := ⟨[], [], [], [], [signature], []⟩
private def catalog : SourceCoreDataCatalog.Catalog := { entries := [
  { sourceType := boxType, definition := some ⟨[.bool]⟩, constructors := [⟨dataId, 0⟩] }] }
private def checked : SourceCoreDataCatalog.Checked := ⟨catalog, DataEnvironment.isWellFormed_sound (by decide)⟩
private def binder : TypedBinder := ⟨⟨owner, 0⟩, "root", .mono boxType, [], false, none⟩
private def source : TypedSource := { owner, inputs := [binder], roots := [], nodes := [] }
private def functions : GenericHeap.PayloadModel catalog where
  Represents := fun _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  extend := fun impossible _ _ => False.elim impossible
private def model := payloadModel catalog signatures functions
private theorem functionTypes : FunctionRuntimeTypes functions := fun impossible => False.elim impossible
private theorem observations : FunctionObservations catalog signatures functions (fun _ _ => False) := fun impossible => False.elim impossible
private theorem faithful : DataEquality.IdentityFaithful (fun _ _ => False) := by constructor <;> intros <;> contradiction
private theorem layouts : CatalogLayouts catalog := by
  apply CatalogLayouts.of_entries
  intro id entry selected
  rcases id with ⟨index⟩
  cases index with
  | zero => cases selected; trivial
  | succ index => simp [catalog] at selected
private def branches : List MemberBranch := [⟨⟨⟨0⟩, 0⟩, [.bool]⟩]
private def route : Route := ⟨boxType, .namedData ⟨0⟩, .bool, [.member ⟨0⟩ 0 branches .bool], none⟩
private def invalid : Word := ⟨23, by decide⟩
private def prepared : Prepared := ⟨route, [.member ⟨0⟩ 0 branches .bool], [], invalid⟩
private theorem preparedBy : prepare checked 5 route invalid (fun _ => Word.zero) = .ok prepared := by cbv
private def projections : List PlaceProjection := [.member "value" 0]
private theorem profile : Profile signatures source boxType projections .bool := by
  refine .member (field := .bool) (signature := signature) (arguments := []) rfl (by cbv) ?_ (.nil rfl)
  intro constructor member
  simp only [signature, List.mem_cons, List.not_mem_nil, or_false] at member
  subst constructor
  rfl
private theorem raw : RawPath checked signatures source boxType (.namedData ⟨0⟩) route.steps projections .bool .bool [] := by
  obtain ⟨_, types, raw⟩ := raw_of_routeSteps profile (show catalog.project boxType = .ok (.namedData ⟨0⟩) by rfl)
    (show catalog.project TypeSystem.Ty.bool = .ok .bool by rfl)
    (show routeSteps checked signatures source (.binder binder.id) binder.id boxType projections = .ok (route.steps, TypeSystem.Ty.bool) by cbv)
  have keys : DataExpressionSequence.Tree source (fun _ _ _ => True) [] [] [] [] := .nil
  have same := raw.keyTypes.tree_types keys
  rw [← same] at raw
  exact raw
private def cell : Dynamic.Cell := ⟨boxType, none, none⟩
private def heap : Dynamic.Heap := ⟨[cell]⟩
private def world : StoreTyping := [OptionalCell.cellType (.namedData ⟨0⟩), .integer]
private def store : Store := [.inLeft (.namedData ⟨0⟩) .unit, .integer 900]
private def environment : Environment := [.cellRef (OptionalCell.cellType (.namedData ⟨0⟩)) 0, .unit]
private def context : Core.Context := [OptionalCell.referenceType (.namedData ⟨0⟩), .unit]
private theorem heapRelated : GenericHeap.HeapRepresents model [0] world heap store := by
  have empty : GenericHeap.HeapRepresents model [] [] ⟨[]⟩ [] := .empty
  exact (empty.allocate (.uninitialized rfl) .append).1.allocate_administrative .integer
private theorem environmentTyped : RuntimeEnvironmentHasTypes world environment context catalog.definitions :=
  .cons (.cellRef rfl) (.cons .unit .nil)
private theorem nonMapping : ¬ ∃ key value, boxType = .mapping key value := by
  intro impossible; obtain ⟨_, _, same⟩ := impossible; cases same
private theorem rootLayout : DataPlaceSnapshot.RootLayout catalog prepared boxType := .ordinary nonMapping rfl
private def expression : Expr := .apply (getter prepared .unit) (.pair (.loadCell (.var 0)) (.var 1))
private theorem ran : runStateful 40 (.initial expression environment store) =
    .done (.inLeft prepared.optionalLeaf (.word invalid)) store := by cbv

example : ∃ futureWorld administrative,
    DataPlaceGetterReflection.ResultRep catalog signatures functions [0] futureWorld prepared (fun _ => Word.zero)
      .bool cell [.member "value" 0] (.inLeft prepared.optionalLeaf (.word invalid)) ∧
    GenericHeap.HeapRepresents model [0] futureWorld heap store ∧
    GeneralHeap.AdministrativePreserved [0] store [0] store ∧ store = store ++ administrative := by
  obtain ⟨futureWorld, administrative, result, _, heaps, _, frame, appended⟩ :=
    DataPlaceGetterReflection.reflects_at functionTypes layouts observations faithful (cell := cell) raw
      (DataPlaceMappingPreparation.steps_of_prepare preparedBy).2.2 (.member .nil) .nil rfl rootLayout
      heapRelated ⟨rfl, rfl⟩ (.intro .head) environmentTyped (infer_sound (by decide))
      (.var rfl) (.var (index := 1) rfl) (runStateful_evaluation_sound ran)
  exact ⟨futureWorld, administrative, result, heaps, frame, appended⟩

private def bareRoute : Route := ⟨boxType, .namedData ⟨0⟩, .namedData ⟨0⟩, [], none⟩
private def barePrepared : Prepared := ⟨bareRoute, [], [], invalid⟩
private def bareExpression : Expr := .apply (getter barePrepared .unit) (.pair (.loadCell (.var 0)) (.var 1))
private theorem bareRan : runStateful 30 (.initial bareExpression environment store) =
    .done (.inRight .word (.inLeft (.namedData ⟨0⟩) .unit)) store := by cbv

/-- An absent bare target is a valid snapshot for a subsequent initializing
assignment. It is not confused with a failure to project an absent value. -/
example : ∃ futureWorld administrative,
    DataPlaceGetterReflection.ResultRep catalog signatures functions [0] futureWorld barePrepared (fun _ => Word.zero)
      boxType cell [] (.inRight .word (.inLeft (.namedData ⟨0⟩) .unit)) ∧
    GenericHeap.HeapRepresents model [0] futureWorld heap store ∧ store = store ++ administrative := by
  obtain ⟨futureWorld, administrative, result, _, heaps, _, _, appended⟩ :=
    DataPlaceGetterReflection.reflects_at (checked := checked) functionTypes layouts observations faithful
      (source := source) (cell := cell) (prepared := barePrepared) (.nil rfl)
      (fuel := 5) (DataPlaceMappingPreparation.Steps.nil 0) .nil .nil rfl (.ordinary nonMapping rfl)
      heapRelated ⟨rfl, rfl⟩ (.intro .head) environmentTyped (infer_sound (by decide))
      (.var rfl) (.var (index := 1) rfl) (runStateful_evaluation_sound bareRan)
  exact ⟨futureWorld, administrative, result, heaps, appended⟩

end Tests.SourceCoreDataPlaceGetterReflection
end

section
-- leanmerge: from Solcore.Test.SourceCoreDataPlaceKeyOrder
/-! A real described/prepared index-member-index route preserves a repeated
index occurrence. Static key certificates come from the production expression
compiler; source projection traces retain each evaluation in order. -/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace Tests.SourceCoreDataPlaceKeyOrder
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open SourceCoreDataPlaces DataPlaceKeyOrder DataPlaceCertificates

private def moduleId : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"place_keys", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def dataId : Resolved.DeclarationId := ⟨moduleId, 1⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "place_keys.solc"⟩, 0, 1⟩
private def site : SourceCoreElaboration.ErrorSite := .occurrence ⟨owner, 0⟩
private def keyId : ExpressionId := ⟨⟨owner, 0⟩⟩
private def innerType : TypeSystem.Ty := .mapping .bool .integer
private def boxType : TypeSystem.Ty := .nominal dataId []
private def outerType : TypeSystem.Ty := .mapping .bool boxType
private def signature : ProgramDataSignature := {
  id := dataId, name := "Box", parameters := []
  constructors := [⟨⟨dataId, 0⟩, "Box", [innerType], ⟨span, ⟨[], ⟨span, "Box"⟩, none⟩⟩⟩]
  source := ⟨span, ⟨none, ⟨span, "Box"⟩, none, span, []⟩⟩ }
private def signatures : ProgramSignatures := ⟨[], [], [], [], [signature], []⟩
private def innerLayout : Core.OrderedMapping.Layout := ⟨.bool, .integer, ⟨0⟩⟩
private def outerLayout : Core.OrderedMapping.Layout := ⟨.bool, .namedData ⟨1⟩, ⟨2⟩⟩
private def catalog : SourceCoreDataCatalog.Catalog := { entries := [
  { sourceType := innerType, definition := some innerLayout.definition },
  { sourceType := boxType, definition := some ⟨[.namedData ⟨0⟩]⟩, constructors := [⟨dataId, 0⟩] },
  { sourceType := outerType, definition := some outerLayout.definition }] }
private def checked : SourceCoreDataCatalog.Checked :=
  ⟨catalog, Core.DataEnvironment.isWellFormed_sound (by decide)⟩
private def binder : TypedBinder := ⟨⟨owner, 0⟩, "root", .mono outerType, [], false, none⟩
private def node : ExpressionNode := {
  id := keyId, span, type := .bool, form := .reference "true" (.builtinBoolean true) }
private def source : TypedSource := { owner, inputs := [binder], roots := [.expression keyId], nodes := [.expression node] }
private def projections : List PlaceProjection := [.index keyId, .member "field" 0, .index keyId]
private def assignment : AssignmentResolution := ⟨⟨binder.id, projections, .integer⟩, []⟩
private def branches : List MemberBranch := [⟨⟨⟨1⟩, 0⟩, [.namedData ⟨0⟩]⟩]
private def route : Route := ⟨outerType, outerLayout.type, .integer,
  [.index outerLayout keyId boxType, .member ⟨1⟩ 0 branches innerLayout.type,
    .index innerLayout keyId .integer], some outerLayout⟩
private theorem described : describe checked signatures source site assignment = .ok route := by cbv
private theorem existsPrepared : (prepare checked 20 route Word.zero (fun _ => Word.zero)).toOption.isSome = true := by cbv
private def prepared : Prepared := (prepare checked 20 route Word.zero (fun _ => Word.zero)).toOption.get existsPrepared
private theorem except_get {α ε : Type} (result : Except ε α) (positive : result.toOption.isSome = true) :
    result = .ok (result.toOption.get positive) := by
  cases result with
  | error => simp [Except.toOption] at positive
  | ok => rfl
private theorem preparedBy : prepare checked 20 route Word.zero (fun _ => Word.zero) = .ok prepared :=
  except_get _ existsPrepared

example : prepared.keys.map Prod.fst = [keyId, keyId] := prepared_source_keys described preparedBy
example : prepared.keys = [(keyId, .bool), (keyId, .bool)] := by cbv

private def scope : Scope := [(binder.id, outerLayout.type)]
private def expression : ExpressionLowerer := fun fuel source scope id reasonAt =>
  SourceCoreBasic.lowerExpression fuel source scope id (reasonAt id)
private def loweredKey : SourceCoreBasic.LoweredExpr := ⟨.bool, LanguageResult.success (.bool true)⟩
private def Child : GenericExpressionMeaning.Certificate := fun scope id code =>
  ∃ depth, BasicExpressions.Tree source scope Word.zero id code.type code.expression depth
private theorem generated : DataPatternValues.ListRel (KeyGenerated expression 20 source scope (fun _ => Word.zero))
    prepared.keys [loweredKey, loweredKey] := by
  have keys : prepared.keys = [(keyId, .bool), (keyId, .bool)] := by cbv
  rw [keys]
  exact .cons ⟨by cbv, rfl⟩ (.cons ⟨by cbv, rfl⟩ .nil)
private theorem unique : NodeOccurrencesUnique source := by
  simp [NodeOccurrencesUnique, nodeOccurrenceIds, source]

private theorem tree_found {scope : Scope} {id : ExpressionId} {type : Core.Ty} {code : Expr} {depth : Nat}
    (tree : BasicExpressions.Tree source scope Word.zero id type code depth) :
    ∃ node, source.lookupExpression? id = some node := by
  cases tree with
  | unit metadata _ | bool _ metadata _ | word _ metadata _ _ | localRead metadata _ _ _
  | group metadata _ _ | pair metadata _ _ _ => exact ⟨_, lookupExpression?_complete unique metadata.contains⟩

/-- The repeated occurrence remains two children in the packed expression.
The static tree is extracted from actual per-key compilation success. -/
example : ∃ types, DataExpressionSequence.Tree source Child scope (sourceKeys projections) types
    [loweredKey, loweredKey] ∧ prepared.keyTypes = [.bool, .bool] := by
  apply tree_of_generated_keys described preparedBy generated
  intro id code accepted
  obtain ⟨type, codeExpression⟩ := code
  obtain ⟨depth, _, tree⟩ := BasicExpressions.tree_of_lowerExpression accepted
  obtain ⟨node, found⟩ := tree_found tree
  exact ⟨node, found, depth, tree⟩

private theorem source_key (program : SourceSemantics.Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (environment : Dynamic.Environment) (heap : Dynamic.Heap) :
    Dynamic.ExpressionEvaluates program context evidence source environment heap keyId (.bool true) heap := by
  have tree : Literals.Tree source keyId (.bool true) 1 :=
    .bool (lookupExpression?_sound (show source.lookupExpression? keyId = some node by cbv)) rfl rfl rfl rfl
  exact tree.source_evaluates program context evidence environment heap

example (program : SourceSemantics.Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (environment : Dynamic.Environment) (heap : Dynamic.Heap) :
    ∃ values, Values projections values [.index (.bool true), .member "field" 0, .index (.bool true)] ∧
      Dynamic.ExpressionsEvaluate program context evidence source environment heap (sourceKeys projections) values heap :=
  projections_values (.index (source_key program context evidence environment heap)
    (.member (.index (source_key program context evidence environment heap) .nil)))

/-- Both fault directions retain the exact failure after any earlier index's
effects; the intervening member adds no expression evaluation. -/
example {program : SourceSemantics.Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
    {before middle after : Dynamic.Heap} {value : Dynamic.Value} {reason : Dynamic.SemanticFault}
    (first : Dynamic.ExpressionEvaluates program context evidence source environment before keyId value middle)
    (second : Dynamic.ExpressionFaults program context evidence source environment middle keyId reason after) :
    Dynamic.SourceProjectionsFault program context evidence source environment before projections reason after :=
  fault_projections (.tail first (.head second))

end Tests.SourceCoreDataPlaceKeyOrder
end

section
-- leanmerge: from Solcore.Test.SourceCoreDataPlaceLayout
/-! A real index/member/index compilation produces the complete static layout,
including all mapping helper receipts and getter typing from the final checker. -/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace Tests.SourceCoreDataPlaceLayout
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open SourceCoreDataPlaces DataPlaceKeyOrder DataPlaceCertificates

private def moduleId : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"place_keys", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def dataId : Resolved.DeclarationId := ⟨moduleId, 1⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "place_keys.solc"⟩, 0, 1⟩
private def site : SourceCoreElaboration.ErrorSite := .occurrence ⟨owner, 0⟩
private def keyId : ExpressionId := ⟨⟨owner, 0⟩⟩
private def innerType : TypeSystem.Ty := .mapping .bool .integer
private def boxType : TypeSystem.Ty := .nominal dataId []
private def outerType : TypeSystem.Ty := .mapping .bool boxType
private def signature : ProgramDataSignature := {
  id := dataId, name := "Box", parameters := []
  constructors := [⟨⟨dataId, 0⟩, "Box", [innerType], ⟨span, ⟨[], ⟨span, "Box"⟩, none⟩⟩⟩]
  source := ⟨span, ⟨none, ⟨span, "Box"⟩, none, span, []⟩⟩ }
private def signatures : ProgramSignatures := ⟨[], [], [], [], [signature], []⟩
private def innerLayout : Core.OrderedMapping.Layout := ⟨.bool, .integer, ⟨0⟩⟩
private def outerLayout : Core.OrderedMapping.Layout := ⟨.bool, .namedData ⟨1⟩, ⟨2⟩⟩
private def catalog : SourceCoreDataCatalog.Catalog := { entries := [
  { sourceType := innerType, definition := some innerLayout.definition },
  { sourceType := boxType, definition := some ⟨[.namedData ⟨0⟩]⟩, constructors := [⟨dataId, 0⟩] },
  { sourceType := outerType, definition := some outerLayout.definition }] }
private def checked : SourceCoreDataCatalog.Checked :=
  ⟨catalog, Core.DataEnvironment.isWellFormed_sound (by decide)⟩
private def binder : TypedBinder := ⟨⟨owner, 0⟩, "root", .mono outerType, [], false, none⟩
private def node : ExpressionNode := {
  id := keyId, span, type := .bool, form := .reference "true" (.builtinBoolean true) }
private def source : TypedSource := { owner, inputs := [binder], roots := [.expression keyId], nodes := [.expression node] }
private def projections : List PlaceProjection := [.index keyId, .member "field" 0, .index keyId]
private def assignment : AssignmentResolution := ⟨⟨binder.id, projections, .integer⟩, []⟩
private def branches : List MemberBranch := [⟨⟨⟨1⟩, 0⟩, [.namedData ⟨0⟩]⟩]
private def route : Route := ⟨outerType, outerLayout.type, .integer,
  [.index outerLayout keyId boxType, .member ⟨1⟩ 0 branches innerLayout.type,
    .index innerLayout keyId .integer], some outerLayout⟩
private theorem described : describe checked signatures source site assignment = .ok route := by cbv
private theorem existsPrepared : (prepare checked 20 route Word.zero (fun _ => Word.zero)).toOption.isSome = true := by cbv
private def prepared : Prepared := (prepare checked 20 route Word.zero (fun _ => Word.zero)).toOption.get existsPrepared
private theorem except_get {α ε : Type} (result : Except ε α) (positive : result.toOption.isSome = true) :
    result = .ok (result.toOption.get positive) := by
  cases result with
  | error => simp [Except.toOption] at positive
  | ok => rfl
private theorem preparedBy : prepare checked 20 route Word.zero (fun _ => Word.zero) = .ok prepared :=
  except_get _ existsPrepared

example : prepared.keys.map Prod.fst = [keyId, keyId] := prepared_source_keys described preparedBy
example : prepared.keys = [(keyId, .bool), (keyId, .bool)] := by cbv

private def scope : Scope := [(binder.id, outerLayout.type)]
private def expression : ExpressionLowerer := fun fuel source scope id reasonAt =>
  SourceCoreBasic.lowerExpression fuel source scope id (reasonAt id)
private def loweredKey : SourceCoreBasic.LoweredExpr := ⟨.bool, LanguageResult.success (.bool true)⟩
private def Child : GenericExpressionMeaning.Certificate := fun scope id code =>
  ∃ depth, BasicExpressions.Tree source scope Word.zero id code.type code.expression depth
private theorem generated : DataPatternValues.ListRel (KeyGenerated expression 20 source scope (fun _ => Word.zero))
    prepared.keys [loweredKey, loweredKey] := by
  have keys : prepared.keys = [(keyId, .bool), (keyId, .bool)] := by cbv
  rw [keys]
  exact .cons ⟨by cbv, rfl⟩ (.cons ⟨by cbv, rfl⟩ .nil)

private theorem rootBinding : rootBinder source assignment.target.root = .ok binder := by cbv
private theorem profile : DataPlaceRouteCertificates.Profile signatures source outerType projections .integer := by
  refine .index rfl (show source.lookupExpression? keyId = some node by cbv) rfl ?_
  refine .member (field := innerType) (signature := signature) (arguments := []) (by rfl) (by cbv) ?_ ?_
  · intro constructor member
    simp only [signature, List.mem_cons, List.not_mem_nil, or_false] at member
    subst constructor
    rfl
  · exact .index rfl (show source.lookupExpression? keyId = some node by cbv) rfl (.nil rfl)

private def body : Expr := execute prepared (.var 0)
  (SourceCoreCalls.packArguments [loweredKey, loweredKey]) (LanguageResult.success (.integer 3))
  (LanguageResult.success .unit) .unit (some .integerAdd) false Word.zero

private theorem bodyChecked : infer? (SourceCoreLocalCell.coreContext scope) body catalog.definitions =
    some (LanguageResult.resultType .unit) := by cbv

private theorem unique : NodeOccurrencesUnique source := by
  simp [NodeOccurrencesUnique, nodeOccurrenceIds, source]
private theorem tree_found {scope : Scope} {id : ExpressionId} {type : Core.Ty} {code : Expr} {depth : Nat}
    (tree : BasicExpressions.Tree source scope Word.zero id type code depth) :
    ∃ node, source.lookupExpression? id = some node := by
  cases tree with
  | unit metadata _ | bool _ metadata _ | word _ metadata _ _ | localRead metadata _ _ _
  | group metadata _ _ | pair metadata _ _ _ => exact ⟨_, lookupExpression?_complete unique metadata.contains⟩

/-- This proof supplies neither a semantic path callback nor a getter typing
proof. Both are extracted from actual compilation and the complete Core check. -/
example (functions : GenericHeap.PayloadModel catalog) :
    ∃ types, DataPlaceResolvedTarget.Layout checked signatures functions source Child scope assignment.target
      prepared [loweredKey, loweredKey] types (SourceCoreLocalCell.coreContext scope) := by
  apply DataPlaceLayoutCertificates.of_describe_prepare (route := route) (expression := expression)
    (reference := .var 0) (rhs := LanguageResult.success (.integer 3))
    (next := LanguageResult.success .unit) (outputType := .unit) (operator := some .integerAdd)
    (bitNot := false) (invalidOperand := Word.zero) ?_ described preparedBy generated ?_ (infer_sound bodyChecked)
  · intro actual accepted
    have same := Except.ok.inj (rootBinding.symm.trans accepted)
    subst actual
    exact profile
  · intro id code accepted
    obtain ⟨type, codeExpression⟩ := code
    obtain ⟨depth, _, tree⟩ := BasicExpressions.tree_of_lowerExpression accepted
    obtain ⟨node, found⟩ := tree_found tree
    exact ⟨node, found, depth, tree⟩

/-- A repeated occurrence retains two key slots in source order. -/
example : prepared.steps.filterMap (fun | .index step => some step.keyPosition | _ => none) = [0, 1] := by cbv

private def scalarBinder : TypedBinder := ⟨⟨owner, 0⟩, "flag", .mono .bool, [], false, none⟩
private def scalarSource : TypedSource := { owner, inputs := [scalarBinder], roots := [.expression keyId], nodes := [.expression node] }
private def scalarScope : Scope := [(scalarBinder.id, .bool)]
private def scalarAssignment : AssignmentResolution := ⟨⟨scalarBinder.id, [], .bool⟩, []⟩
private def scalarPrepared : Prepared := ⟨⟨.bool, .bool, .bool, [], none⟩, [], [], Word.zero⟩
private def scalarBody : Expr := execute scalarPrepared (.var 0) (SourceCoreCalls.packArguments [])
  (LanguageResult.success (.bool true)) (LanguageResult.success .unit) .unit none false Word.zero
private def ScalarChild : GenericExpressionMeaning.Certificate := fun scope id code =>
  ∃ depth, BasicExpressions.Tree scalarSource scope Word.zero id code.type code.expression depth

private theorem scalarCompiled : lower checked signatures expression 20 scalarSource scalarScope site
    scalarAssignment .equal (some keyId) .unit (LanguageResult.success .unit) (fun _ => Word.zero)
    Word.zero Word.zero (fun _ => Word.zero) = .ok scalarBody := by cbv
private theorem scalarChecked : infer? (SourceCoreLocalCell.coreContext scalarScope) scalarBody catalog.definitions =
    some (LanguageResult.resultType .unit) := by cbv
private theorem scalarUnique : NodeOccurrencesUnique scalarSource := by
  simp [NodeOccurrencesUnique, nodeOccurrenceIds, scalarSource]

private theorem scalar_tree_found {scope : Scope} {id : ExpressionId} {type : Core.Ty} {code : Expr} {depth : Nat}
    (tree : BasicExpressions.Tree scalarSource scope Word.zero id type code depth) :
    ∃ node, scalarSource.lookupExpression? id = some node := by
  cases tree with
  | unit metadata _ | bool _ metadata _ | word _ metadata _ _ | localRead metadata _ _ _
  | group metadata _ _ | pair metadata _ _ _ => exact ⟨_, lookupExpression?_complete scalarUnique metadata.contains⟩

/-- Full production `lower` success, rather than a separately supplied route,
now produces the layout and exact execute equation. -/
example (functions : GenericHeap.PayloadModel catalog) :
    ∃ prepared codes sourceTypes index value,
      SourceCoreLocalCell.lookup? scalarScope scalarAssignment.target.root = some (index, prepared.route.rootType) ∧
      DataPlaceResolvedTarget.Layout checked signatures functions scalarSource ScalarChild scalarScope
        scalarAssignment.target prepared codes sourceTypes (SourceCoreLocalCell.coreContext scalarScope) ∧
      RhsGenerated expression 20 scalarSource scalarScope (fun _ => Word.zero) prepared.route.leafType (some keyId) value ∧
      scalarBody = execute prepared (.var index) (SourceCoreCalls.packArguments codes) value
        (LanguageResult.success .unit) .unit (binaryOperator (prepared.route.leafType = .integer) .equal) false Word.zero := by
  apply DataPlaceLayoutCertificates.of_lower (invalid := Word.zero) (missing := fun _ => Word.zero)
    (resultType := LanguageResult.resultType .unit) ?_ ?_ scalarCompiled (infer_sound scalarChecked)
  · intro actual accepted
    have known : rootBinder scalarSource scalarAssignment.target.root = .ok scalarBinder := by cbv
    have same := Except.ok.inj (known.symm.trans accepted)
    subst actual
    exact .nil rfl
  · intro id code accepted
    obtain ⟨type, codeExpression⟩ := code
    obtain ⟨depth, _, tree⟩ := BasicExpressions.tree_of_lowerExpression accepted
    obtain ⟨node, found⟩ := scalar_tree_found tree
    exact ⟨node, found, depth, tree⟩

end Tests.SourceCoreDataPlaceLayout
end

section
-- leanmerge: from Solcore.Test.SourceCoreDataPlaceModifier
/-! Typed modifier success and source fault exclusion cover every Word/Integer
assignment spelling. Concrete checks retain zero-divisor behavior, negative
bitwise behavior, and plain assignment's independence from the old snapshot. -/

set_option autoImplicit false
namespace Tests.SourceCoreDataPlaceModifier
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open SourceCoreDataPlaces DataEquality DataPayload DataPlaceModifier

private def catalog : SourceCoreDataCatalog.Catalog := {}
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def functions : GenericHeap.PayloadModel catalog where
  Represents := fun _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  extend := fun impossible _ _ => False.elim impossible

/-- Each source operator has a total initialized primitive result at Word, and
each but the shifts at Integer. This covers Word wrapping, division/modulo by
zero and every Integer sign without a runtime evaluation premise. The store can
include arbitrary closure/cell cycles. -/
example (operator : Syntax.ValueAssignOp) (left right : Word) (store : Store) :
    ∃ result value, ValueRep catalog signatures functions [] [] .word result value .word ∧
      Dynamic.AssignmentValueApplies operator (some (.word left)) (.word right) result ∧
      Evaluates [.inRight .unit (.word left), .word right] store
        (modified .word (binaryOperator false operator) false (.var 0) (.var 1) Word.zero)
        (.inRight .word value) store ∧
      ¬ Dynamic.AssignmentOperandsInvalid operator (some (.word left)) (.word right) :=
  initialized_success (.inl rfl) (.word left) (.word right) (.var rfl) (.var rfl) store Word.zero

example (operator : Syntax.ValueAssignOp) (notWordOnly : operator.wordOnly = false) (left right : Int) (store : Store) :
    ∃ result value, ValueRep catalog signatures functions [] [] .integer result value .integer ∧
      Dynamic.AssignmentValueApplies operator (some (.integer left)) (.integer right) result ∧
      Evaluates [.inRight .unit (.integer left), .integer right] store
        (modified .integer (binaryOperator true operator) false (.var 0) (.var 1) Word.zero)
        (.inRight .word value) store ∧
      ¬ Dynamic.AssignmentOperandsInvalid operator (some (.integer left)) (.integer right) :=
  initialized_success (.inr ⟨rfl, notWordOnly⟩) (.integer left) (.integer right) (.var rfl) (.var rfl) store Word.zero

example (left : Int) (store : Store) :
    ∃ value, ValueRep catalog signatures functions [] [] .integer (.integer 0) value .integer ∧
      Evaluates [.inRight .unit (.integer left), .integer 0] store
        (modified .integer (binaryOperator true .divide) false (.var 0) (.var 1) Word.zero)
        (.inRight .word value) store ∧
      ¬ Dynamic.AssignmentOperandsInvalid .divide (some (.integer left)) (.integer 0) :=
  initialized_preserves (.inr ⟨rfl, rfl⟩) (.integer left) (.integer 0) (.divide (.integerDivideZero left))
    (.var rfl) (.var rfl) store Word.zero

private def integerCode (operator : Syntax.ValueAssignOp) : Expr :=
  modified .integer (binaryOperator true operator) false (.var 0) (.var 1) Word.zero
example : infer? [.sum .unit .integer, .integer] (integerCode .divide) = some (.sum .word .integer) := by cbv
example : runStateful 30 (.initial (integerCode .divide) [.inRight .unit (.integer (-7)), .integer 0] [.integer 900]) =
    .done (.inRight .word (.integer 0)) [.integer 900] := by cbv
example : runStateful 30 (.initial (integerCode .modulo) [.inRight .unit (.integer (-7)), .integer 0] [.integer 900]) =
    .done (.inRight .word (.integer 0)) [.integer 900] := by cbv
example : runStateful 30 (.initial (integerCode .divide) [.inRight .unit (.integer (-7)), .integer 3] []) =
    .done (.inRight .word (.integer (-3))) [] := by cbv
example : runStateful 30 (.initial (integerCode .modulo) [.inRight .unit (.integer (-7)), .integer 3] []) =
    .done (.inRight .word (.integer 2)) [] := by cbv
example : runStateful 30 (.initial (integerCode .bitXor) [.inRight .unit (.integer (-7)), .integer 3] []) =
    .done (.inRight .word (.integer (-6))) [] := by cbv

/-- Plain assignment can initialize an absent value. Even an unused malformed
snapshot expression is skipped; only the already evaluated RHS is selected. -/
example : Evaluates [.integer 17] []
    (modified .integer none false (.apply .unit .unit) (.var 0) Word.zero) (.inRight .word (.integer 17)) [] :=
  equal_modified (.var rfl) [] Word.zero
example : ¬ Dynamic.AssignmentOperandsInvalid .equal none (.integer 17) :=
  assignment_excludes_invalid (.equal none (.integer 17))

/-- The initialized condition is necessary: compound assignment of an absent
snapshot still returns its language fault and has an independent source fault. -/
example : Dynamic.AssignmentOperandsInvalid .add none (.integer 17) := .uninitialized (by decide)
example : runStateful 30 (.initial (integerCode .add) [.inLeft .integer .unit, .integer 17] []) =
    .done (.inLeft .integer (.word Word.zero)) [] := by cbv

example (value : Word) (store : Store) : Dynamic.BitNotSnapshot (some (.word value)) (.word value.bitNot) ∧
    Evaluates [.inRight .unit (.word value)] store
      (modified .word none true (.var 0) (.apply .unit .unit) Word.zero)
      (.inRight .word (.word value.bitNot)) store ∧
    ¬ Dynamic.UnaryPrimitiveOperandInvalid .bitNot (.word value) :=
  word_bitNot_success value (.var rfl) none store Word.zero

/-- Integer unary behavior is tested as its primitive relation, since the
separate independent bit-not-assignment rule currently accepts only Word. -/
example : Dynamic.UnaryPrimitiveApplies .bitNot (.integer (-7)) (.integer 6) ∧
    Evaluates [.inRight .unit (.integer (-7))] []
      (modified .integer none true (.var 0) .unit Word.zero) (.inRight .word (.integer 6)) [] ∧
    ¬ Dynamic.UnaryPrimitiveOperandInvalid .bitNot (.integer (-7)) :=
  integer_bitNot_primitive (-7) (.var rfl) none [] Word.zero

end Tests.SourceCoreDataPlaceModifier
end

section
-- leanmerge: from Solcore.Test.SourceCoreDataPlaceModifierReflection
/-! Modifier reflection distinguishes an absent compound-assignment snapshot
from ordinary initialization, and constructs the source primitive result for
any completed typed Word operation without assuming its source application. -/
set_option autoImplicit false
namespace Tests.SourceCoreDataPlaceModifierReflection
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open SourceCoreDataPlaces DataPayload DataPlaceModifierReflection

private def catalog : SourceCoreDataCatalog.Catalog := {}
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def functions : GenericHeap.PayloadModel catalog where
  Represents := fun _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  extend := fun impossible _ _ => False.elim impossible

example (operator : Syntax.ValueAssignOp) (left right : Word) (before after : Store) (result : Value)
    (completed : Evaluates [.inRight .unit (.word left), .word right] before
      (modified .word (binaryOperator false operator) false (.var 0) (.var 1) Word.zero) result after) :
    after = before ∧ ∃ source value,
      Dynamic.AssignmentValueApplies operator (some (.word left)) (.word right) source ∧
      ValueRep catalog signatures functions [] [] .word source value .word ∧ result = .inRight .word value := by
  obtain ⟨sameStore, related⟩ := reflects (catalog := catalog) (signatures := signatures) (functions := functions)
    (.inr (.inl rfl)) (.present (.word left)) (.word right) (.var rfl) (.var (index := 1) rfl) completed
  refine ⟨sameStore, ?_⟩
  cases related with
  | applied applied value => exact ⟨_, _, applied, value, rfl⟩
  | uninitialized absent => cases absent

private def token : Word := ⟨17, by decide⟩
private def absentAdd : Expr := modified .integer (binaryOperator true .add) false (.var 0) (.var 1) token
private theorem absentRan : runStateful 30 (.initial absentAdd [.inLeft .integer .unit, .integer 5] [.integer 900]) =
    .done (.inLeft .integer (.word token)) [.integer 900] := by cbv

example : Dynamic.AssignmentOperandsInvalid .add none (.integer 5) := by
  have result := reflects (catalog := catalog) (signatures := signatures) (functions := functions)
    (mapping := []) (world := []) (.inr (.inr ⟨rfl, rfl⟩)) .absent (.integer 5)
    (.var rfl) (.var (index := 1) rfl) (runStateful_evaluation_sound absentRan)
  exact result.2.invalid.2.2

private def initializeCode : Expr := modified .bool (binaryOperator false .equal) false (.var 0) (.var 1) token
private theorem initializeRan : runStateful 30 (.initial initializeCode [.inLeft .bool .unit, .bool true] [.integer 900]) =
    .done (.inRight .word (.bool true)) [.integer 900] := by cbv

example : ∃ source, Dynamic.AssignmentValueApplies .equal none (.bool true) source ∧
    ValueRep catalog signatures functions [] [] .bool source (.bool true) .bool := by
  have result := reflects (catalog := catalog) (signatures := signatures) (functions := functions)
    (mapping := []) (world := []) (.inl rfl) .absent (.bool true)
    (.var rfl) (.var (index := 1) rfl) (runStateful_evaluation_sound initializeRan)
  cases result.2 with
  | applied applied related => exact ⟨_, applied, related⟩

end Tests.SourceCoreDataPlaceModifierReflection
end

section
-- leanmerge: from Solcore.Test.SourceCoreDataPlacePrefixReflection
/-! The actual whole execute expression reflects its source target before RHS
evaluation. Empty-key certificates use a vacuous universal child theorem; named
member failure suppresses a visible RHS write, and bare initialization exposes
the actual three-slot continuation as an output witness. -/
set_option autoImplicit false
set_option maxRecDepth 16384
namespace Tests.SourceCoreDataPlacePrefixReflection
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open SourceCoreDataPlaces DataPayload DataPlaceRouteCertificates

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"getter_reflection", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def dataId : Resolved.DeclarationId := ⟨moduleId, 1⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "getter_reflection.solc"⟩, 0, 1⟩
private def boxType : TypeSystem.Ty := .nominal dataId []
private def signature : ProgramDataSignature := {
  id := dataId, name := "Box", parameters := []
  constructors := [⟨⟨dataId, 0⟩, "Box", [.bool], ⟨span, ⟨[], ⟨span, "Box"⟩, none⟩⟩⟩]
  source := ⟨span, ⟨none, ⟨span, "Box"⟩, none, span, []⟩⟩ }
private def signatures : ProgramSignatures := ⟨[], [], [], [], [signature], []⟩
private def catalog : SourceCoreDataCatalog.Catalog := { entries := [
  { sourceType := boxType, definition := some ⟨[.bool]⟩, constructors := [⟨dataId, 0⟩] }] }
private def checked : SourceCoreDataCatalog.Checked := ⟨catalog, DataEnvironment.isWellFormed_sound (by decide)⟩
private def binder : TypedBinder := ⟨⟨owner, 0⟩, "root", .mono boxType, [], false, none⟩
private def source : TypedSource := { owner, inputs := [binder], roots := [], nodes := [] }
private def functions : GenericHeap.PayloadModel catalog where
  Represents := fun _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  extend := fun impossible _ _ => False.elim impossible
private def model := payloadModel catalog signatures functions
private theorem functionTypes : FunctionRuntimeTypes functions := fun impossible => False.elim impossible
private theorem observations : FunctionObservations catalog signatures functions (fun _ _ => False) := fun impossible => False.elim impossible
private theorem faithful : DataEquality.IdentityFaithful (fun _ _ => False) := by constructor <;> intros <;> contradiction
private theorem layouts : CatalogLayouts catalog := by
  apply CatalogLayouts.of_entries
  intro id entry selected
  rcases id with ⟨index⟩
  cases index with
  | zero => cases selected; trivial
  | succ index => simp [catalog] at selected
private def branches : List MemberBranch := [⟨⟨⟨0⟩, 0⟩, [.bool]⟩]
private def route : Route := ⟨boxType, .namedData ⟨0⟩, .bool, [.member ⟨0⟩ 0 branches .bool], none⟩
private def invalid : Word := ⟨23, by decide⟩
private def prepared : Prepared := ⟨route, [.member ⟨0⟩ 0 branches .bool], [], invalid⟩
private theorem preparedBy : prepare checked 5 route invalid (fun _ => Word.zero) = .ok prepared := by cbv
private def projections : List PlaceProjection := [.member "value" 0]
private theorem profile : Profile signatures source boxType projections .bool := by
  refine .member (field := .bool) (signature := signature) (arguments := []) rfl (by cbv) ?_ (.nil rfl)
  intro constructor member
  simp only [signature, List.mem_cons, List.not_mem_nil, or_false] at member
  subst constructor
  rfl
private theorem raw : RawPath checked signatures source boxType (.namedData ⟨0⟩) route.steps projections .bool .bool [] := by
  obtain ⟨_, types, raw⟩ := raw_of_routeSteps profile (show catalog.project boxType = .ok (.namedData ⟨0⟩) by rfl)
    (show catalog.project TypeSystem.Ty.bool = .ok .bool by rfl)
    (show routeSteps checked signatures source (.binder binder.id) binder.id boxType projections = .ok (route.steps, TypeSystem.Ty.bool) by cbv)
  have keys : DataExpressionSequence.Tree source (fun _ _ _ => True) [] [] [] [] := .nil
  have same := raw.keyTypes.tree_types keys
  rw [← same] at raw
  exact raw
private def cell : Dynamic.Cell := ⟨boxType, none, none⟩
private def heap : Dynamic.Heap := ⟨[cell]⟩
private def world : StoreTyping := [OptionalCell.cellType (.namedData ⟨0⟩), .integer]
private def store : Store := [.inLeft (.namedData ⟨0⟩) .unit, .integer 900]
private def environment : Environment := [.cellRef (OptionalCell.cellType (.namedData ⟨0⟩)) 0, .unit]
private def context : Core.Context := [OptionalCell.referenceType (.namedData ⟨0⟩), .unit]
private theorem heapRelated : GenericHeap.HeapRepresents model [0] world heap store := by
  have empty : GenericHeap.HeapRepresents model [] [] ⟨[]⟩ [] := .empty
  exact (empty.allocate (.uninitialized rfl) .append).1.allocate_administrative .integer
private theorem environmentTyped : RuntimeEnvironmentHasTypes world environment context catalog.definitions :=
  .cons (.cellRef rfl) (.cons .unit .nil)
private theorem nonMapping : ¬ ∃ key value, boxType = .mapping key value := by
  intro impossible; obtain ⟨_, _, same⟩ := impossible; cases same
private theorem rootLayout : DataPlaceSnapshot.RootLayout catalog prepared boxType := .ordinary nonMapping rfl
private def scope : Scope := [(binder.id, .namedData ⟨0⟩)]
private def sourceEnvironment : Dynamic.Environment := [(binder.id, ⟨0⟩)]
private def sourceContext := (SourceSemantics.Context.ofSignatures signatures).withLocal binder.id binder.scheme
private def place : PlaceResolution := ⟨binder.id, projections, .bool⟩
private def Child : GenericExpressionMeaning.Certificate := fun _ _ _ => False
private def faults : GenericExpressionMeaning.FaultRep := fun _ _ => True
private theorem meaning (program : SourceSemantics.Program) :
    GenericExpressionMeaning.Reflects model program sourceContext [] source Child faults := by
  intro scope id lowered impossible
  exact impossible.elim
private theorem environments : DataHeap.EnvRepresents catalog [0] world [.unit] scope sourceEnvironment environment :=
  .cons ⟨rfl, rfl⟩ (.nil (.cons .unit .nil))
private theorem locals : Dynamic.EnvironmentAgrees heap sourceContext.locals sourceEnvironment :=
  .cons (.intro .head) rfl (.ordinary rfl rfl) .nil
private theorem targetLayout : DataPlaceResolvedTarget.Layout checked signatures functions source Child scope place
    prepared [] [] (SourceCoreLocalCell.coreContext scope ++ [.unit]) := by
  refine ⟨.nil, rfl, rootLayout, ?_, infer_sound (by decide)⟩
  intro mapping world sources values evaluated shaped related
  cases shaped with
  | member shaped =>
    cases shaped
    cases related
    exact raw.prepared_path (DataPlaceMappingPreparation.steps_of_prepare preparedBy).2.2
      (.member .nil) .nil (allKeys := []) (by intro i value impossible; simp at impossible)
private def skippedRhs : Expr := .letE (.storeCell (.var 0) (.inRight .unit (.construct ⟨⟨0⟩, 0⟩ (.bool true))))
  (LanguageResult.success (.bool true))
private def expression : Expr := execute prepared (.var 0) (SourceCoreCalls.packArguments []) skippedRhs
  (LanguageResult.success .unit) .unit none false Word.zero
private theorem ran : runStateful 100 (.initial expression environment store) =
    .done (.inLeft .unit (.word invalid)) store := by cbv
private theorem reflected (program : SourceSemantics.Program) :
    DataPlacePrefixReflection.Result checked signatures functions program sourceContext [] source faults prepared [] [] place
      sourceEnvironment environment heap store [0] world skippedRhs (LanguageResult.success .unit) .unit none false Word.zero
      (.inLeft .unit (.word invalid)) store :=
  DataPlacePrefixReflection.reflects targetLayout raw (DataPlaceMappingPreparation.steps_of_prepare preparedBy).2.2
    (meaning program) functionTypes layouts observations faithful (fun _ => trivial) environments heapRelated locals rfl
    .head (.intro .head) rfl trivial (runStateful_evaluation_sound ran)

/-- Both the ordinary source cell and sentinel remain untouched because target
resolution fails before entering the RHS's storeCell. The independent fault is
constructed by whole-prefix reflection, rather than supplied to it. -/
example (program : SourceSemantics.Program) :
    ∃ reason after finalMap finalWorld,
      Dynamic.SourcePlaceFaults program sourceContext [] source sourceEnvironment heap place reason after ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after store ∧
      GeneralHeap.AdministrativePreserved [0] store finalMap store := by
  have result := reflected program
  cases result with
  | fault sourceFault resultEq tokenRep heaps maps worlds frame metadata => exact ⟨_, _, _, _, sourceFault, heaps, frame⟩
  | resolved sourceTrace execution continuation =>
    cases sourceTrace with
    | intro lookup initialRead evaluate currentRead initialValue selection =>
      have locationEq := lookup.functional (show Dynamic.Environment.LooksUp sourceEnvironment place.root ⟨0⟩ from .head)
      cases locationEq
      cases evaluate with
      | member evaluate =>
        cases evaluate
        have cellEq := currentRead.functional (show Dynamic.Heap.Reads heap ⟨0⟩ cell from .intro .head)
        cases cellEq
        cases initialValue with
        | uninitialized => cases selection

private def bareRoute : Route := ⟨boxType, .namedData ⟨0⟩, .namedData ⟨0⟩, [], none⟩
private def barePrepared : Prepared := ⟨bareRoute, [], [], invalid⟩
private def barePlace : PlaceResolution := ⟨binder.id, [], boxType⟩
private theorem bareLayout : DataPlaceResolvedTarget.Layout checked signatures functions source Child scope barePlace
    barePrepared [] [] (SourceCoreLocalCell.coreContext scope ++ [.unit]) := by
  refine ⟨.nil, rfl, .ordinary nonMapping rfl, ?_, infer_sound (by decide)⟩
  intro mapping world sources values projections shaped related
  cases shaped
  exact ⟨0, .nil rfl⟩
private def rhs : Expr := LanguageResult.success (.construct ⟨⟨0⟩, 0⟩ (.bool true))
private def bareExpression : Expr := execute barePrepared (.var 0) (SourceCoreCalls.packArguments []) rhs
  (LanguageResult.success .unit) .unit none false Word.zero
private def finalStore : Store := [.inRight .unit (.constructed ⟨⟨0⟩, 0⟩ (.bool true)), .integer 900]
private theorem bareRan : runStateful 100 (.initial bareExpression environment store) = .done (.inRight .word .unit) finalStore := by cbv

/-- The resolved branch carries its actual empty snapshot and the remaining
RHS/write/continuation evaluation under three administrative slots. -/
example (program : SourceSemantics.Program) : ∃ target after, ∃ execution : DataPlaceResolvedTarget.Execution checked signatures functions barePrepared [] [] barePlace target
      environment store [0] world heap after,
    Dynamic.SourcePlaceResolves program sourceContext [] source sourceEnvironment heap barePlace target after ∧
    Evaluates (DataPlaceExecution.snapshotEnvironment barePrepared.route.rootType execution.target
      (DataPatternValues.packValues execution.values) execution.snapshot environment) execution.store
      (DataPlacePrefixReflection.remainder barePrepared .unit rhs (LanguageResult.success .unit) .unit none false Word.zero)
      (.inRight .word .unit) finalStore := by
  have result := DataPlacePrefixReflection.reflects (checked := checked) bareLayout
    (steps := []) (.nil rfl) (fuel := 5) (missing := fun _ => Word.zero) (.nil 0)
    (meaning program) functionTypes layouts observations faithful (fun _ => trivial) environments heapRelated locals rfl
    .head (.intro .head) rfl trivial (runStateful_evaluation_sound bareRan)
  cases result with
  | fault sourceFault resultEq => cases resultEq
  | resolved sourceTrace execution continuation => exact ⟨_, _, execution, sourceTrace, continuation⟩

end Tests.SourceCoreDataPlacePrefixReflection
end

section
-- leanmerge: from Solcore.Test.SourceCoreDataPlaceProofs
/-! Actual generated member helpers and independent source place semantics.
The last example observes the snapshot before the RHS and reconstruction from
the latest root, including a changed constructor and an untouched sibling. -/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
namespace Tests.SourceCoreDataPlaceProofs
open Solcore Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open SourceCoreDataPlaces DataPlaceMembers DataPlaceCertificates DataPatternTypedValues

private def moduleId : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"data_place_proofs", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def dataId : Resolved.DeclarationId := ⟨moduleId, 1⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "data_place_proofs.solc"⟩, 0, 1⟩
private def site : SourceCoreElaboration.ErrorSite := .occurrence ⟨owner, 0⟩
private def boxType : TypeSystem.Ty := .nominal dataId []
private def constructorSource (name : String) : Syntax.EnumConstructor :=
  ⟨span, ⟨[], ⟨span, name⟩, none⟩⟩
private def signature : ProgramDataSignature := {
  id := dataId, name := "Box", parameters := []
  constructors := [
    ⟨⟨dataId, 0⟩, "A", [.integer, .integer], constructorSource "A"⟩,
    ⟨⟨dataId, 1⟩, "B", [.integer, .integer], constructorSource "B"⟩]
  source := ⟨span, ⟨none, ⟨span, "Box"⟩, none, span, []⟩⟩
}
private def signatures : ProgramSignatures := ⟨[], [], [], [], [signature], []⟩
private def catalog : SourceCoreDataCatalog.Catalog := { entries := [{
  sourceType := boxType
  definition := some ⟨[.product .integer .integer, .product .integer .integer]⟩
  constructors := [⟨dataId, 0⟩, ⟨dataId, 1⟩]
}] }
private def checked : SourceCoreDataCatalog.Checked :=
  ⟨catalog, Core.DataEnvironment.isWellFormed_sound (by decide)⟩
private def binder : TypedBinder := ⟨⟨owner, 0⟩, "box", .mono boxType, [], false, none⟩
private def source : TypedSource := { owner, inputs := [binder], roots := [], nodes := [] }
private def assignment : AssignmentResolution := ⟨⟨binder.id, [.member "first" 0], .integer⟩, []⟩
private def branches : List MemberBranch := [⟨⟨⟨0⟩, 0⟩, [.integer, .integer]⟩, ⟨⟨⟨0⟩, 1⟩, [.integer, .integer]⟩]
private def route : Route := ⟨boxType, .namedData ⟨0⟩, .integer, [.member ⟨0⟩ 0 branches .integer], none⟩
private def prepared : Prepared := ⟨route, [.member ⟨0⟩ 0 branches .integer], [], Core.Word.zero⟩
private def metadata (index : Nat) : DataConstructorInstantiation := ⟨⟨dataId, index⟩, [], [.integer, .integer], boxType⟩

private theorem memberAccepted : memberStep checked signatures site binder.id boxType 0 =
    .ok (.member ⟨0⟩ 0 branches .integer, .integer) := by cbv
private theorem described : describe checked signatures source site assignment = .ok route := by cbv
private theorem preparedBy : prepare checked 20 route (Core.Word.zero) (fun _ => Core.Word.zero) = .ok prepared := by cbv

private theorem uniform : DataPlaceMemberCertificates.Uniform signature [] 0 .integer := by
  intro constructor member
  simp only [signature, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> rfl

/-- The layout proof is extracted from successful member compilation and exact
source uniformity; no hand-supplied branch certificate or child evaluation is
needed. -/
private theorem memberLayout : MemberLayout checked signatures boxType .integer ⟨0⟩ 0 branches := by
  obtain ⟨identity, emitted, fieldType, _, sameStep, certificate⟩ :=
    DataPlaceMemberCertificates.certificate_of_memberStep (by rfl) (by rfl) (by cbv) uniform memberAccepted
  cases sameStep
  exact DataPlaceMemberCertificates.Certificate.layout (by rfl) (by cbv) certificate

private theorem routed : routeSteps checked signatures source site binder.id boxType [.member "first" 0] =
    .ok (route.steps, .integer) := by cbv
private theorem profile : DataPlaceMemberCertificates.Profile signatures boxType [.member "first" 0] .integer :=
  .member (by rfl) (by rfl) (by cbv) uniform .nil

/-- Route and prepare receipts automatically produce the exact semantic path. -/
private theorem members : Members checked signatures boxType prepared.steps [.member "first" 0] .integer := by
  obtain ⟨_, _, _, _, resolved, names, members⟩ :=
    DataPlaceMemberCertificates.route_prepare_members profile routed preparedBy
  cases names with
  | member tail => cases tail; exact members
private def sourceValue (index : Nat) (first second : Int) : Dynamic.Value :=
  .constructed (metadata index) [.integer first, .integer second]
private def coreValue (index : Nat) (first second : Int) : Core.Value :=
  .constructed ⟨⟨0⟩, index⟩ (.pair (.integer first) (.integer second))
private theorem representsA (first second : Int) :
    TypedValueRep catalog signatures boxType (sourceValue 0 first second) (coreValue 0 first second) :=
  .constructed (metadata := metadata 0) (values := [.integer first, .integer second]) (by rfl) rfl (by cbv)
    (.cons (.integer _) (.cons (.integer _) .nil))
private theorem representsB (first second : Int) :
    TypedValueRep catalog signatures boxType (sourceValue 1 first second) (coreValue 1 first second) :=
  .constructed (metadata := metadata 1) (values := [.integer first, .integer second]) (by rfl) rfl (by cbv)
    (.cons (.integer _) (.cons (.integer _) .nil))

example : Dynamic.ProjectionsRead (some (sourceValue 0 7 1)) [.member "first" 0] (some (.integer 7)) :=
  .member .head .nil
example : Dynamic.ProjectionsUpdate (fun _ updated => updated = .integer 12)
    (some (sourceValue 1 8 900)) [.member "first" 0] (sourceValue 1 12 900) :=
  .member .head (.leaf rfl) .head

/-- The helper theorem derives all generated child evaluations. Its input
representation authenticates the nominal metadata against the actual catalog. -/
example (environment : Core.Environment) (store : Core.Store) :
    ∃ updatedSource updatedCore, TypedValueRep catalog signatures boxType updatedSource updatedCore ∧
      Dynamic.ProjectionsUpdate (fun _ updated => updated = .integer 12)
        (some (sourceValue 1 8 900)) [.member "first" 0] updatedSource ∧
      (∃ required, ∀ fuel, required ≤ fuel →
        Core.runStateful fuel (.initial (.apply (SourceCoreDataPlaces.setter prepared .unit) (.var 0))
          (.pair (.inRight .unit (coreValue 1 8 900)) (.pair .unit (.integer 12)) :: environment) store) =
          .done (.inRight .word updatedCore) store) ∧
      (∀ fuel actual finalStore,
        Core.runStateful fuel (.initial (.apply (SourceCoreDataPlaces.setter prepared .unit) (.var 0))
          (.pair (.inRight .unit (coreValue 1 8 900)) (.pair .unit (.integer 12)) :: environment) store) = .done actual finalStore →
        actual = .inRight .word updatedCore ∧ finalStore = store) :=
  Members.setter_run members prepared rfl rfl (representsB 8 900) (.integer 12) environment store .unit .unit

example : Core.infer? [] (getter prepared .unit) catalog.definitions =
    some (.function (.product (.sum .unit (.namedData ⟨0⟩)) .unit) (.sum .word (.sum .unit .integer))) := by cbv
example : Core.infer? [] (SourceCoreDataPlaces.setter prepared .unit) catalog.definitions =
    some (.function (.product (.sum .unit (.namedData ⟨0⟩)) (.product .unit .integer)) (.sum .word (.namedData ⟨0⟩))) := by cbv
private def sentinel : Core.Store := [.integer 1000, .cellRef .integer 0]
example : Core.runStateful 1000 (.initial (.apply (getter prepared .unit) (.var 0))
    [.pair (.inRight .unit (coreValue 0 7 1)) .unit] sentinel) =
    .done (.inRight .word (.inRight .unit (.integer 7))) sentinel := by cbv
example : Core.runStateful 1000 (.initial (.apply (SourceCoreDataPlaces.setter prepared .unit) (.var 0))
    [.pair (.inRight .unit (coreValue 1 8 900)) (.pair .unit (.integer 12))] sentinel) =
    .done (.inRight .word (coreValue 1 12 900)) sentinel := by cbv
example : Core.runStateful 1000 (.initial (.apply (getter prepared .unit) (.var 0))
    [.pair (.inLeft (.namedData ⟨0⟩) .unit) .unit] sentinel) =
    .done (.inLeft (.sum .unit .integer) (.word (Core.Word.zero))) sentinel := by cbv

private def scope : Scope := [(binder.id, .namedData ⟨0⟩)]
private def rhsId : ExpressionId := ⟨⟨owner, 1⟩⟩
private def rhsExpression : Core.Expr :=
  .letE (.storeCell (.var 0) (.inRight .unit (.construct ⟨⟨0⟩, 1⟩ (.pair (.integer 8) (.integer 900)))))
    (Core.LanguageResult.success (.integer 5))
private def expression : ExpressionLowerer := fun _ _ _ id _ =>
  if id = rhsId then .ok ⟨.integer, rhsExpression⟩ else .error (.missingExpression id)
private def next : Core.Expr := Core.OptionalCell.read (.namedData ⟨0⟩) (.var 0) (Core.Word.zero)
private def lowered : Core.Expr := execute prepared (.var 0) (SourceCoreCalls.packArguments []) rhsExpression next
  (.namedData ⟨0⟩) (some .integerAdd) false (Core.Word.zero)
private theorem accepted : lower checked signatures expression 20 source scope site assignment .add (some rhsId)
    (.namedData ⟨0⟩) next (fun _ => Core.Word.zero) (Core.Word.zero) (Core.Word.zero)
    (fun _ => Core.Word.zero) = .ok lowered := by cbv
example : Generated checked signatures expression 20 source scope site assignment .add (some rhsId)
    (.namedData ⟨0⟩) next (fun _ => Core.Word.zero) (Core.Word.zero) (Core.Word.zero)
    (fun _ => Core.Word.zero) lowered := generated_of_lower accepted

/-- The RHS changes the root from A(7,1) to B(8,900). Compound addition uses
snapshot 7, then writes 12 into the latest B while preserving its second field. -/
example : Core.infer? [Core.OptionalCell.referenceType (.namedData ⟨0⟩)] lowered catalog.definitions =
    some (.sum .word (.namedData ⟨0⟩)) := by cbv
example : Core.runStateful 1000 (.initial lowered
    [.cellRef (.sum .unit (.namedData ⟨0⟩)) 0] [.inRight .unit (coreValue 0 7 1)]) =
    .done (.inRight .word (coreValue 1 12 900)) [.inRight .unit (coreValue 1 12 900)] := by cbv

end Tests.SourceCoreDataPlaceProofs
end

section
-- leanmerge: from Solcore.Test.SourceCoreDataPlaceReadReflection
/-! Actual mixed mapping/member selectors reflect both found values and
missing defaults. No independent source projection trace is supplied to the
reflection theorem. Administrative cells retain the input store prefix. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 2400000
set_option cbv.maxSteps 2000000
namespace Tests.SourceCoreDataPlaceReadReflection
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open SourceCoreDataPlaces DataPayload DataPlaceRouteCertificates

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"read_reflection", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def dataId : Resolved.DeclarationId := ⟨moduleId, 1⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "read_reflection.solc"⟩, 0, 1⟩
private def keyId : ExpressionId := ⟨⟨owner, 0⟩⟩
private def boxType : TypeSystem.Ty := .nominal dataId []
private def mappingType : TypeSystem.Ty := .mapping .bool boxType
private def signature : ProgramDataSignature := {
  id := dataId, name := "Box", parameters := []
  constructors := [⟨⟨dataId, 0⟩, "Box", [.integer], ⟨span, ⟨[], ⟨span, "Box"⟩, none⟩⟩⟩]
  source := ⟨span, ⟨none, ⟨span, "Box"⟩, none, span, []⟩⟩ }
private def signatures : ProgramSignatures := ⟨[], [], [], [], [signature], []⟩
private def mapLayout : Core.OrderedMapping.Layout := ⟨.bool, .namedData ⟨0⟩, ⟨1⟩⟩
private def catalog : SourceCoreDataCatalog.Catalog := { entries := [
  { sourceType := boxType, definition := some ⟨[.integer]⟩, constructors := [⟨dataId, 0⟩] },
  { sourceType := mappingType, definition := some mapLayout.definition }] }
private def checked : SourceCoreDataCatalog.Checked := ⟨catalog, Core.DataEnvironment.isWellFormed_sound (by decide)⟩
private def binder : TypedBinder := ⟨⟨owner, 0⟩, "root", .mono mappingType, [], false, none⟩
private def node : ExpressionNode := { id := keyId, span, type := .bool, form := .reference "true" (.builtinBoolean true) }
private def source : TypedSource := { owner, inputs := [binder], roots := [.expression keyId], nodes := [.expression node] }
private def projections : List PlaceProjection := [.index keyId, .member "value" 0]
private def branches : List MemberBranch := [⟨⟨⟨0⟩, 0⟩, [.integer]⟩]
private def route : Route := ⟨mappingType, mapLayout.type, .integer,
  [.index mapLayout keyId boxType, .member ⟨0⟩ 0 branches .integer], some mapLayout⟩
private def token : Word := ⟨19, by decide⟩
private theorem preparationExists : (prepare checked 20 route Word.zero (fun _ => token)).toOption.isSome = true := by cbv
private def prepared : Prepared := (prepare checked 20 route Word.zero (fun _ => token)).toOption.get preparationExists
private theorem except_get {α ε : Type} (result : Except ε α) (positive : result.toOption.isSome = true) :
    result = .ok (result.toOption.get positive) := by
  cases result with
  | error => simp [Except.toOption] at positive
  | ok => rfl
private theorem preparedBy : prepare checked 20 route Word.zero (fun _ => token) = .ok prepared :=
  except_get _ preparationExists
private def functions : GenericHeap.PayloadModel catalog where
  Represents := fun _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  extend := fun impossible _ _ => False.elim impossible
private theorem functionTypes : FunctionRuntimeTypes functions := fun impossible => False.elim impossible
private theorem observations : FunctionObservations catalog signatures functions (fun _ _ => False) :=
  fun impossible => False.elim impossible
private theorem faithful : DataEquality.IdentityFaithful (fun _ _ => False) := by
  constructor <;> intros <;> contradiction
private theorem registered : mapLayout.Registered catalog.definitions := ⟨.bool, .namedData rfl, rfl⟩
private theorem layouts : CatalogLayouts catalog := by
  apply CatalogLayouts.of_entries
  intro id entry selected
  rcases id with ⟨index⟩
  cases index with
  | zero => cases selected; trivial
  | succ index => cases index with
    | zero => cases selected; exact ⟨.bool, .namedData ⟨0⟩, rfl, rfl, registered⟩
    | succ index => simp [catalog] at selected
private theorem profile : Profile signatures source mappingType projections .integer := by
  refine .index rfl (show source.lookupExpression? keyId = some node by cbv) rfl ?_
  refine .member (field := .integer) (signature := signature) (arguments := []) rfl (by cbv) ?_ (.nil rfl)
  intro constructor member
  simp only [signature, List.mem_cons, List.not_mem_nil, or_false] at member
  subst constructor
  rfl
private theorem raw : RawPath checked signatures source mappingType mapLayout.type route.steps projections .integer .integer [.bool] := by
  obtain ⟨_, types, raw⟩ := raw_of_routeSteps profile (show catalog.project mappingType = .ok mapLayout.type by rfl)
    (show catalog.project TypeSystem.Ty.integer = .ok .integer by rfl)
    (show routeSteps checked signatures source (.occurrence keyId.occurrence) binder.id mappingType projections =
      .ok (route.steps, TypeSystem.Ty.integer) by cbv)
  have keyTree : DataExpressionSequence.Tree source (fun _ _ _ => True) [] [keyId] [.bool]
      [⟨.bool, LanguageResult.success (.bool true)⟩] := .single (show source.lookupExpression? keyId = some node by cbv) trivial
  have same := raw.keyTypes.tree_types keyTree
  rw [← same] at raw
  exact raw
private theorem shaped : DataPlaceKeyOrder.Values projections [.bool true] [.index (.bool true), .member "value" 0] :=
  .index (.member .nil)
private theorem keysRelated : DataExpressionSequence.Values (payloadModel catalog signatures functions) [] []
    [.bool] [.bool] [.bool true] [.bool true] := .cons (.bool true) .nil
private def metadata : DataConstructorInstantiation := ⟨⟨dataId, 0⟩, [], [.integer], boxType⟩
private def sourceBox : Dynamic.Value := .constructed metadata [.integer 7]
private def coreBox : Value := .constructed ⟨⟨0⟩, 0⟩ (.integer 7)
private theorem boxRelated : ValueRep catalog signatures functions [] [] boxType sourceBox coreBox (.namedData ⟨0⟩) :=
  .constructed (metadata := metadata) (tag := ⟨⟨0⟩, 0⟩) (declaration := dataId) (arguments := [])
    rfl rfl (by cbv) rfl rfl (.cons (.integer 7) .nil)
private def fullRoot : Dynamic.Value := .mapping .bool boxType [(.bool true, sourceBox)]
private def fullCore : Value := Core.OrderedMapping.encode mapLayout [(.bool true, coreBox)]
private theorem fullRelated : ValueRep catalog signatures functions [] [] mappingType fullRoot fullCore mapLayout.type :=
  .mapping rfl rfl rfl registered (.prepend (.bool true) boxRelated (.empty _ _ _ _))
private def emptyRoot : Dynamic.Value := .mapping .bool boxType []
private def emptyCore : Value := Core.OrderedMapping.encode mapLayout []
private theorem emptyRelated : ValueRep catalog signatures functions [] [] mappingType emptyRoot emptyCore mapLayout.type :=
  .mapping rfl rfl rfl registered (.empty _ _ _ _)
private def selector : Expr := select prepared prepared.steps (.var 0) (.var 1)
private def before : Store := [.integer 900]
private def finalStore (root : Value) : Store := match runStateful 500 (.initial selector [root, .bool true] before) with
  | .done _ store => store
  | _ => []
private theorem fullRan : runStateful 500 (.initial selector [fullCore, .bool true] before) =
    .done (.inRight .word (.inRight .unit (.integer 7))) (finalStore fullCore) := by cbv
private theorem emptyRan : runStateful 500 (.initial selector [emptyCore, .bool true] before) =
    .done (.inLeft prepared.optionalLeaf (.word token)) (finalStore emptyCore) := by cbv

/-- All source outcomes are inferred from the generated selector's run. -/
example : ∃ selected value,
    Dynamic.ProjectionsRead (some fullRoot) [.index (.bool true), .member "value" 0] (some selected) ∧
    ValueRep catalog signatures functions [] [] .integer selected value .integer ∧
    value = .integer 7 := by
  obtain ⟨administrative, count, appended, bound, path, reflected⟩ := DataPlaceReadReflection.reflects
    functionTypes layouts observations faithful raw (DataPlaceMappingPreparation.steps_of_prepare preparedBy).2.2
    shaped keysRelated (by cbv) fullRelated (DataEquality.Selects.var rfl) (DataEquality.Selects.var (index := 1) rfl)
    (runStateful_evaluation_sound fullRan)
  rcases reflected with ⟨selected, value, read, related, same⟩ | ⟨reason, token, fault, impossible⟩
  · exact ⟨selected, value, read, related, (Value.inRight.inj (Value.inRight.inj same).2).2.symm⟩
  · cases impossible

example : ∃ reason, Dynamic.ProjectionsFaults (some emptyRoot) [.index (.bool true), .member "value" 0] reason := by
  obtain ⟨administrative, count, appended, bound, path, reflected⟩ := DataPlaceReadReflection.reflects
    functionTypes layouts observations faithful raw (DataPlaceMappingPreparation.steps_of_prepare preparedBy).2.2
    shaped keysRelated (by cbv) emptyRelated (DataEquality.Selects.var rfl) (DataEquality.Selects.var (index := 1) rfl)
    (runStateful_evaluation_sound emptyRan)
  rcases reflected with ⟨selected, value, read, related, impossible⟩ | ⟨reason, token, fault, same⟩
  · cases impossible
  · exact ⟨reason, fault⟩

example : (finalStore fullCore).length = before.length + 3 := by cbv
example : (finalStore emptyCore)[0]? = some (.integer 900) := by cbv

/-- Metadata-only typing for both concrete closure models does not require
source captured-cell validity or an assumption about running the body. -/
example (catalog : SourceCoreDataCatalog.Catalog) (program : SourceSemantics.Program) (certificate : FunctionCode.BodyCertificate)
    (policy : SourceCoreFunctions.Policy) : FunctionRuntimeTypes (FunctionValues.model catalog program certificate policy) :=
  ordinary_function_runtimeTypes catalog program certificate policy
example (catalog : SourceCoreDataCatalog.Catalog) (program : SourceSemantics.Program) (certificate : FunctionCode.BodyCertificate)
    (table : SourceCoreStageCodebook.Table) : FunctionRuntimeTypes (ContractedFunctionValues.model catalog program certificate table) :=
  contracted_function_runtimeTypes catalog program certificate table

end Tests.SourceCoreDataPlaceReadReflection
end

section
-- leanmerge: from Solcore.Test.SourceCoreDataPlaceMappingProofs
/-! Actual preparation receipts, independent mapping read/update semantics,
finite helper execution, and preservation of an existing source heap frame.
Runtime regressions exercise the same emitted code and its checker. -/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace Tests.SourceCoreDataPlaceMappingProofs
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open SourceCoreDataPlaces DataPlaceMappingIndex DataPlaceMappingHelpers DataEquality DataEqualityValues

private def moduleId : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"mapping_place_proofs", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def keyId : ExpressionId := ⟨⟨owner, 0⟩⟩
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def layout : Core.OrderedMapping.Layout := ⟨.integer, .integer, ⟨0⟩⟩
private def catalog : SourceCoreDataCatalog.Catalog := { entries := [
  { sourceType := .mapping .integer .integer, definition := some layout.definition }]
}
private def checked : SourceCoreDataCatalog.Checked :=
  ⟨catalog, Core.DataEnvironment.isWellFormed_sound (by decide)⟩
private def route : Route := ⟨.mapping .integer .integer, layout.type, .integer,
  [.index layout keyId .integer], some layout⟩
private def missing : TypeSystem.Ty → Word := fun _ => Word.zero
private theorem noIdentities : IdentityFaithful (fun _ _ => False) := by
  constructor <;> intros <;> contradiction
private abbrev ValueRep := DataPatternTypedValues.TypedValueRep catalog signatures .integer
private def sources : List (Dynamic.Value × Dynamic.Value) :=
  [(.integer 7, .integer 11), (.integer 7, .integer 22), (.integer 9, .integer 33)]
private def entries : Core.OrderedMapping.Entries :=
  [(.integer 7, .integer 11), (.integer 7, .integer 22), (.integer 9, .integer 33)]
private def root : Value := Core.OrderedMapping.encode layout entries
private def getterArgument : Value := .pair (.inRight .unit root) (.integer 7)
private def getterArgumentType : Core.Ty := .product (.sum .unit layout.type) .integer
private def sentinelHeap : Dynamic.Heap := ⟨[⟨.integer, some (.integer 900), none⟩]⟩
private def sentinelStore : Store := [.inRight .unit (.integer 900)]
private def sentinelWorld : StoreTyping := [.sum .unit .integer]
private def model := GenericHeap.finitePayload catalog signatures
private theorem sentinelRelated : GenericHeap.HeapRepresents model [0] sentinelWorld sentinelHeap sentinelStore := by
  have empty : GenericHeap.HeapRepresents model [] [] ⟨[]⟩ [] := .empty
  have represented : model.Represents [] [] .integer (.integer 900) (.integer 900) .integer :=
    ⟨rfl, .integer 900⟩
  exact (empty.allocate (.initialized represented) .append).1
private theorem layoutRegistered : layout.Registered catalog.definitions := ⟨.integer, .integer, rfl⟩
private theorem argumentTyped : RuntimeValueHasType sentinelWorld getterArgument getterArgumentType catalog.definitions := by
  apply RuntimeValueHasType.pair (RuntimeValueHasType.inRight ?_) RuntimeValueHasType.integer
  apply Core.OrderedMapping.encode_hasType layoutRegistered entries
  intro key value member
  simp only [entries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same | same <;> cases same <;> exact ⟨.integer, .integer⟩

/-- Preparation supplies all comparison/default programs. The checker premise
is the real final helper check, rather than an assumed semantic evaluation.
All existing source cells and their aliases survive the new helper cells. -/
example (prepared : Prepared)
    (accepted : prepare checked 20 route Word.zero missing = .ok prepared)
    (checkedGetter : infer? [getterArgumentType] (.apply (getter prepared .integer) (.var 0)) catalog.definitions =
      some (.sum .word (.sum .unit .integer))) :
    ∃ finalStore futureWorld administrative,
      Dynamic.ProjectionsRead (some (.mapping .integer .integer sources)) [.index (.integer 7)] (some (.integer 11)) ∧
      WorldExtends sentinelWorld futureWorld ∧
      GenericHeap.HeapRepresents model [0] futureWorld sentinelHeap finalStore ∧
      GeneralHeap.AdministrativePreserved [0] sentinelStore [0] finalStore ∧
      finalStore = sentinelStore ++ administrative ∧ administrative.length = 2 ∧
      (∃ required, ∀ fuel, required ≤ fuel → runStateful fuel
        (.initial (.apply (getter prepared .integer) (.var 0)) [getterArgument] sentinelStore) =
          .done (.inRight .word (.inRight .unit (.integer 11))) finalStore) ∧
      (∀ fuel value actualStore, runStateful fuel
        (.initial (.apply (getter prepared .integer) (.var 0)) [getterArgument] sentinelStore) =
          .done value actualStore → value = .inRight .word (.inRight .unit (.integer 11)) ∧ actualStore = finalStore) := by
  obtain ⟨index, ⟨certificate⟩, steps, keys, indexLayout, position, _⟩ :=
    single_index_of_prepare accepted rfl (by rfl) (by rfl) (by rfl) (by rfl)
  have routeSame := (DataPlaceMappingPreparation.steps_of_prepare accepted).1
  have rootMapping : prepared.route.rootMapping = some index.layout := by rw [routeSame, indexLayout]; rfl
  have keyRep (n : Int) : KeyRep certificate signatures (fun _ _ => False) (.integer n) (.integer n) := by
    change Observation _ _ _ certificate.comparison.type _ _
    rw [← certificate.keyType, indexLayout]
    exact .integer n
  have related : OrderedMapping.EntriesRel (KeyRep certificate signatures (fun _ _ => False)) ValueRep sources entries :=
    .cons (keyRep 7) (.integer 11) (.cons (keyRep 7) (.integer 22) (.cons (keyRep 9) (.integer 33) .nil))
  have input : RootInput index.layout .integer .integer (KeyRep certificate signatures (fun _ _ => False)) ValueRep
      ⟨.mapping .integer .integer, some (.mapping .integer .integer sources), none⟩
      (.inRight .unit root) sources entries := by simpa only [root, indexLayout] using RootInput.initialized related
  obtain ⟨value, finalStore, administrative, _, projections, represented, evaluated, extension, count⟩ :=
    getter_preserves certificate prepared steps rootMapping noIdentities input (keyRep 7)
      (.found (.head ⟨rfl, .integer 7⟩)) [getterArgument] sentinelStore .integer [.integer 7] (.var 0)
      (by simp [Prepared.keyTypes, keys]) (by simp [position]) (.var rfl)
  have valueSame : value = .integer 11 := by
    rcases represented with represented | ⟨_, tree⟩
    · cases represented; rfl
    · cases tree
  subst value
  obtain ⟨futureWorld, worlds, heap, _, administrativeFrame⟩ := DataMappingHeap.evaluation_preserves_frame
    sentinelRelated (.cons argumentTyped .nil) (infer_sound checkedGetter) evaluated extension
  refine ⟨finalStore, futureWorld, administrative, projections, worlds, heap, administrativeFrame,
    extension, count, evaluation_runStateful_complete_with_sufficient_fuel evaluated, ?_⟩
  intro fuel value actualStore ran
  exact evaluation_deterministic (runStateful_evaluation_sound ran) evaluated

private def updatedSources : List (Dynamic.Value × Dynamic.Value) :=
  [(.integer 7, .integer 55), (.integer 7, .integer 22), (.integer 9, .integer 33)]

/-- Duplicate keys keep their order; only the first equivalent occurrence is
replaced. The supplied root is the latest root passed into the setter. -/
example (prepared : Prepared) (accepted : prepare checked 20 route Word.zero missing = .ok prepared) :
    ∃ output finalStore administrative,
      Dynamic.ProjectionsUpdate (fun _ value => value = .integer 55)
        (some (.mapping .integer .integer sources)) [.index (.integer 7)] (.mapping .integer .integer updatedSources) ∧
      Evaluates [.pair (.inRight .unit root) (.pair (.integer 7) (.integer 55))] sentinelStore
        (.apply (setter prepared .integer) (.var 0)) (.inRight .word output) finalStore ∧
      finalStore = sentinelStore ++ administrative ∧ administrative.length = 4 := by
  obtain ⟨index, ⟨certificate⟩, steps, keys, indexLayout, position, _⟩ :=
    single_index_of_prepare accepted rfl (by rfl) (by rfl) (by rfl) (by rfl)
  have routeSame := (DataPlaceMappingPreparation.steps_of_prepare accepted).1
  have rootMapping : prepared.route.rootMapping = some index.layout := by rw [routeSame, indexLayout]; rfl
  have keyRep (n : Int) : KeyRep certificate signatures (fun _ _ => False) (.integer n) (.integer n) := by
    change Observation _ _ _ certificate.comparison.type _ _
    rw [← certificate.keyType, indexLayout]
    exact .integer n
  have related : OrderedMapping.EntriesRel (KeyRep certificate signatures (fun _ _ => False)) ValueRep sources entries :=
    .cons (keyRep 7) (.integer 11) (.cons (keyRep 7) (.integer 22) (.cons (keyRep 9) (.integer 33) .nil))
  have input : RootInput index.layout .integer .integer (KeyRep certificate signatures (fun _ _ => False)) ValueRep
      ⟨.mapping .integer .integer, some (.mapping .integer .integer sources), none⟩
      (.inRight .unit root) sources entries := by simpa only [root, indexLayout] using RootInput.initialized related
  obtain ⟨output, finalStore, administrative, _, updated, _, evaluated, extension, count⟩ :=
    setter_preserves certificate prepared steps rootMapping noIdentities input (keyRep 7) (DataPatternTypedValues.TypedValueRep.integer 55)
      (.found (.head ⟨rfl, .integer 7⟩)) (.update (.head ⟨rfl, .integer 7⟩))
      [.pair (.inRight .unit root) (.pair (.integer 7) (.integer 55))] sentinelStore .integer [.integer 7] (.var 0)
      (by simp [Prepared.keyTypes, keys]) (by simp [position]) (.var rfl)
  exact ⟨output, finalStore, administrative, updated, evaluated, extension, count⟩

/-- An uninitialized root is read as the empty mapping without writing that
virtual value into the source cell. The scalar default is derived automatically. -/
example (prepared : Prepared) (accepted : prepare checked 20 route Word.zero missing = .ok prepared) :
    ∃ finalStore administrative,
      Dynamic.RootInitialValue ⟨.mapping .integer .integer, none, none⟩ (some (.mapping .integer .integer [])) ∧
      Dynamic.ProjectionsRead (some (.mapping .integer .integer [])) [.index (.integer 8)] (some (.integer 0)) ∧
      Evaluates [.pair (.inLeft layout.type .unit) (.integer 8)] sentinelStore
        (.apply (getter prepared .integer) (.var 0)) (.inRight .word (.inRight .unit (.integer 0))) finalStore ∧
      finalStore = sentinelStore ++ administrative ∧ administrative.length = 2 := by
  obtain ⟨index, ⟨certificate⟩, steps, keys, indexLayout, position, _⟩ :=
    single_index_of_prepare accepted rfl (by rfl) (by rfl) (by rfl) (by rfl)
  have routeSame := (DataPlaceMappingPreparation.steps_of_prepare accepted).1
  have rootMapping : prepared.route.rootMapping = some index.layout := by rw [routeSame, indexLayout]; rfl
  have keyRep : KeyRep certificate signatures (fun _ _ => False) (.integer 8) (.integer 8) := by
    change Observation _ _ _ certificate.comparison.type _ _
    rw [← certificate.keyType, indexLayout]
    exact .integer 8
  have input : RootInput index.layout .integer .integer (KeyRep certificate signatures (fun _ _ => False)) ValueRep
      ⟨.mapping .integer .integer, none, none⟩ (.inLeft layout.type .unit) [] [] := by
    simpa only [indexLayout] using (RootInput.absent (layout := index.layout))
  obtain ⟨value, finalStore, administrative, initial, projections, represented, evaluated, extension, count⟩ :=
    getter_preserves certificate prepared steps rootMapping noIdentities input keyRep (.default .nil .integer)
      [.pair (.inLeft layout.type .unit) (.integer 8)] sentinelStore .integer [.integer 8] (.var 0)
      (by simp [Prepared.keyTypes, keys]) (by simp [position]) (.var rfl)
  have valueSame : value = .integer 0 := by
    rcases represented with represented | ⟨_, tree⟩
    · cases represented; rfl
    · cases tree; rfl
  subst value
  exact ⟨finalStore, administrative, initial, projections, evaluated, extension, count⟩

private def functionLayout : Core.OrderedMapping.Layout := ⟨.integer, TaggedFunction.functionType .unit .unit, ⟨0⟩⟩
private def functionCatalog : SourceCoreDataCatalog.Catalog := { entries := [
  { sourceType := .mapping .integer (.function .unit .unit), definition := some functionLayout.definition }]
}
private def functionChecked : SourceCoreDataCatalog.Checked :=
  ⟨functionCatalog, Core.DataEnvironment.isWellFormed_sound (by decide)⟩
private def functionRoute : Route := ⟨.mapping .integer (.function .unit .unit), functionLayout.type,
  functionLayout.valueType, [.index functionLayout keyId (.function .unit .unit)], some functionLayout⟩
private def anonymous : Value := .pair (.inLeft .word .unit)
  (.closure .unit (.sum .word .unit) (.inRight .word .unit) [])

/-- Missing function defaults remain source language faults. In particular the
setter does not insert the supplied closure or allocate insertion helpers. -/
example (prepared : Prepared)
    (accepted : prepare functionChecked 20 functionRoute Word.zero missing = .ok prepared) :
    ∃ finalStore administrative,
      Dynamic.ProjectionsFaults (some (.mapping .integer (.function .unit .unit) [])) [.index (.integer 8)]
        (.missingMappingDefault (.function .unit .unit)) ∧
      Evaluates [.pair (.inLeft functionLayout.type .unit) (.pair (.integer 8) anonymous)] sentinelStore
        (.apply (setter prepared .integer) (.var 0)) (.inLeft functionLayout.type (.word Word.zero)) finalStore ∧
      finalStore = sentinelStore ++ administrative ∧ administrative.length = 2 := by
  obtain ⟨index, ⟨certificate⟩, steps, keys, indexLayout, position, reason⟩ :=
    single_index_of_prepare accepted rfl (by rfl) (by rfl) (by rfl) (by rfl)
  have routeSame := (DataPlaceMappingPreparation.steps_of_prepare accepted).1
  have rootMapping : prepared.route.rootMapping = some index.layout := by rw [routeSame, indexLayout]; rfl
  have keyRep : KeyRep certificate signatures (fun _ _ => False) (.integer 8) (.integer 8) := by
    change Observation _ _ _ certificate.comparison.type _ _
    rw [← certificate.keyType, indexLayout]
    exact .integer 8
  have input : RootInput index.layout .integer (.function .unit .unit)
      (KeyRep certificate signatures (fun _ _ => False)) (fun _ _ => False)
      ⟨.mapping .integer (.function .unit .unit), none, none⟩ (.inLeft functionLayout.type .unit) [] [] := by
    simpa only [indexLayout] using (RootInput.absent (layout := index.layout))
  obtain ⟨finalStore, administrative, _, failed, evaluated, extension, count⟩ :=
    setter_missing certificate prepared steps rootMapping noIdentities input keyRep (.integer 8) .nil (by intro impossible; cases impossible)
      [.pair (.inLeft functionLayout.type .unit) (.pair (.integer 8) anonymous)] sentinelStore .integer [.integer 8] (.var 0)
      (by simp [Prepared.keyTypes, keys]) (by simp [position]) (.var rfl)
  exact ⟨finalStore, administrative, failed, by simpa only [indexLayout, reason, missing] using evaluated, extension, count⟩

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)
private def checkResult (expected : Value) (adminCount : Nat) (result : StatefulRunResult) : IO Unit := do
  match result with
  | .done value store =>
    assertTrue (value == expected) "generated mapping helper returned wrong value or entry order"
    assertTrue (store.length == sentinelStore.length + adminCount) "generated mapping helper has wrong allocation count"
    assertTrue (store.take sentinelStore.length == sentinelStore) "generated mapping helper overwrote an existing source cell"
  | other => throw (IO.userError s!"generated mapping helper did not finish: {reprStr other}")
private def checkHelper (layout : Core.OrderedMapping.Layout) (catalog : SourceCoreDataCatalog.Catalog)
    (prepared : Prepared) (write : Bool) (argument expected : Value) (adminCount : Nat) : IO Unit := do
  let helper := if write then setter prepared layout.keyType else getter prepared layout.keyType
  let argumentType := if write then .product (.sum .unit layout.type) (.product layout.keyType layout.valueType)
    else .product (.sum .unit layout.type) layout.keyType
  let resultType := if write then layout.type else .sum .unit layout.valueType
  let expression := .apply helper (.var 0)
  assertTrue (infer? [argumentType] expression catalog.definitions == some (.sum .word resultType)) "generated mapping helper failed Core checker"
  let initial := Core.State.initial expression [argument] sentinelStore
  checkResult expected adminCount (runStateful 5000 initial)
  match runStateful 8 initial with
  | .outOfFuel checkpoint => checkResult expected adminCount (runStateful 5000 checkpoint)
  | other => throw (IO.userError s!"mapping helper checkpoint unexpectedly finished: {reprStr other}")

private def checkRun := checkHelper layout catalog

private def wordLayout : Core.OrderedMapping.Layout := ⟨.word, .integer, ⟨0⟩⟩
private def wordCatalog : SourceCoreDataCatalog.Catalog := { entries := [
  { sourceType := .mapping .word .integer, definition := some wordLayout.definition }]
}
private def wordChecked : SourceCoreDataCatalog.Checked :=
  ⟨wordCatalog, Core.DataEnvironment.isWellFormed_sound (by decide)⟩
private def wordRoute : Route := ⟨.mapping .word .integer, wordLayout.type, .integer,
  [.index wordLayout keyId .integer], some wordLayout⟩

def run : IO Unit := do
  let prepared ← match prepare checked 20 route Word.zero missing with
    | .ok value => pure value
    | .error error => throw (IO.userError s!"actual mapping preparation rejected: {reprStr error}")
  checkRun prepared false getterArgument (.inRight .word (.inRight .unit (.integer 11))) 2
  checkRun prepared false (.pair (.inRight .unit root) (.integer 8)) (.inRight .word (.inRight .unit (.integer 0))) 2
  checkRun prepared false (.pair (.inLeft layout.type .unit) (.integer 8)) (.inRight .word (.inRight .unit (.integer 0))) 2
  let updated := Core.OrderedMapping.encode layout [(.integer 7, .integer 55), (.integer 7, .integer 22), (.integer 9, .integer 33)]
  checkRun prepared true (.pair (.inRight .unit root) (.pair (.integer 7) (.integer 55))) (.inRight .word updated) 4
  let appended := Core.OrderedMapping.encode layout (entries ++ [(.integer 8, .integer 55)])
  checkRun prepared true (.pair (.inRight .unit root) (.pair (.integer 8) (.integer 55))) (.inRight .word appended) 4
  let fresh := Core.OrderedMapping.encode layout [(.integer 8, .integer 55)]
  checkRun prepared true (.pair (.inLeft layout.type .unit) (.pair (.integer 8) (.integer 55))) (.inRight .word fresh) 4
  let functionPrepared ← match prepare functionChecked 20 functionRoute Word.zero missing with
    | .ok value => pure value
    | .error error => throw (IO.userError s!"function mapping preparation rejected: {reprStr error}")
  checkHelper functionLayout functionCatalog functionPrepared false
    (.pair (.inLeft functionLayout.type .unit) (.integer 8))
    (.inLeft (.sum .unit functionLayout.valueType) (.word Word.zero)) 2
  checkHelper functionLayout functionCatalog functionPrepared true
    (.pair (.inLeft functionLayout.type .unit) (.pair (.integer 8) anonymous))
    (.inLeft functionLayout.type (.word Word.zero)) 2
  let wordPrepared ← match prepare wordChecked 20 wordRoute Word.zero missing with
    | .ok value => pure value
    | .error error => throw (IO.userError s!"Word mapping preparation rejected: {reprStr error}")
  let wordEntries := [(.word Word.zero, .integer 11), (.word Word.zero, .integer 22)]
  let wordRoot := Core.OrderedMapping.encode wordLayout wordEntries
  checkHelper wordLayout wordCatalog wordPrepared false (.pair (.inRight .unit wordRoot) (.word Word.zero))
    (.inRight .word (.inRight .unit (.integer 11))) 2
  checkHelper wordLayout wordCatalog wordPrepared true
    (.pair (.inRight .unit wordRoot) (.pair (.word Word.zero) (.integer 55)))
    (.inRight .word (Core.OrderedMapping.encode wordLayout [(.word Word.zero, .integer 55), (.word Word.zero, .integer 22)])) 4
  IO.println "source Core mapping place proof consumers GREEN"

end Tests.SourceCoreDataPlaceMappingProofs
end

section
-- leanmerge: from Solcore.Test.SourceCoreDataPlacePathFaults
/-! A default-created inner mapping whose function value has no default.
Both nested lookup helpers run, but neither insertion nor the replacement
expression runs after the inner failure. -/
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreDataPlacePathFaults
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open SourceCoreDataPlaces DataPlaceMappingIndex DataEquality DataEqualityValues DataPatternValues
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"place_path_faults", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def keyId (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def functionType : TypeSystem.Ty := .function .unit .unit
private def innerType : TypeSystem.Ty := .mapping .integer functionType
private def innerLayout : Core.OrderedMapping.Layout := ⟨.integer, TaggedFunction.functionType .unit .unit, ⟨0⟩⟩
private def outerLayout : Core.OrderedMapping.Layout := ⟨.integer, innerLayout.type, ⟨1⟩⟩
private def catalog : SourceCoreDataCatalog.Catalog := { entries := [
  { sourceType := innerType, definition := some innerLayout.definition },
  { sourceType := .mapping .integer innerType, definition := some outerLayout.definition }]
}
private def checked : SourceCoreDataCatalog.Checked := ⟨catalog, Core.DataEnvironment.isWellFormed_sound (by decide)⟩
private def route : Route := ⟨.mapping .integer innerType, outerLayout.type, innerLayout.valueType,
  [.index outerLayout (keyId 0) innerType, .index innerLayout (keyId 1) functionType], some outerLayout⟩
private theorem except_get {α ε : Type} (result : Except ε α) (positive : result.toOption.isSome = true) :
    result = .ok (result.toOption.get positive) := by
  cases result with
  | error => simp [Except.toOption] at positive
  | ok value => rfl
private theorem comparisonExists : (SourceCoreDataEquality.prepare 20 checked .integer).toOption.isSome = true := by cbv
private def comparison := (SourceCoreDataEquality.prepare 20 checked .integer).toOption.get comparisonExists
private theorem comparisonGenerated : SourceCoreDataEquality.prepare 20 checked .integer = .ok comparison := except_get _ comparisonExists
private theorem innerDefaultExists : (SourceCoreDefaultValue.prepare (functionType.size + 1) checked functionType).toOption.isSome = true := by cbv
private def innerDefault := (SourceCoreDefaultValue.prepare (functionType.size + 1) checked functionType).toOption.get innerDefaultExists
private theorem innerDefaultGenerated : SourceCoreDefaultValue.prepare (functionType.size + 1) checked functionType = .ok innerDefault := except_get _ innerDefaultExists
private theorem outerDefaultExists : (SourceCoreDefaultValue.prepare (innerType.size + 1) checked innerType).toOption.isSome = true := by cbv
private def outerDefault := (SourceCoreDefaultValue.prepare (innerType.size + 1) checked innerType).toOption.get outerDefaultExists
private theorem outerDefaultGenerated : SourceCoreDefaultValue.prepare (innerType.size + 1) checked innerType = .ok outerDefault := except_get _ outerDefaultExists
private def innerIndex : PreparedIndex := ⟨innerLayout, keyId 1, 1, comparison.expression, innerDefault.expression, Word.zero⟩
private def outerIndex : PreparedIndex := ⟨outerLayout, keyId 0, 0, comparison.expression, outerDefault.expression, Word.zero⟩
private def prepared : Prepared := ⟨route, [.index outerIndex, .index innerIndex], [(keyId 0, .integer), (keyId 1, .integer)], Word.zero⟩
private def innerCertificate : Index checked functionType innerIndex := Index.of_generated comparisonGenerated innerDefaultGenerated rfl rfl
private def outerCertificate : Index checked innerType outerIndex := Index.of_generated comparisonGenerated outerDefaultGenerated rfl rfl
private theorem accepted : prepare checked 20 route Word.zero (fun _ => Word.zero) = .ok prepared := by
  have inner : checked.catalog.entries[0]? = some ⟨innerType, some innerLayout.definition, []⟩ := rfl
  have outer : checked.catalog.entries[1]? = some ⟨.mapping .integer innerType, some outerLayout.definition, []⟩ := rfl
  have innerDefaultCompiled := innerDefaultGenerated
  have outerDefaultCompiled := outerDefaultGenerated
  simp only [innerType, functionType] at innerDefaultCompiled outerDefaultCompiled
  simp [prepare, route, innerLayout, outerLayout, inner, outer, innerType,
    comparisonGenerated, innerDefaultCompiled, outerDefaultCompiled, functionType,
    prepared, innerIndex, outerIndex, bind, Except.bind, pure, Except.pure, Except.mapError]
private theorem comparisonType : comparison.type = .integer := by
  have projection := comparison.projection
  rw [DataPlaceMappingPreparation.comparison_sourceType comparisonGenerated] at projection
  exact Except.ok.inj projection.symm
private theorem noIdentities : IdentityFaithful (fun _ _ => False) := by
  constructor <;> intros <;> contradiction
private theorem innerKey : KeyRep innerCertificate signatures (fun _ _ => False) (.integer 7) (.integer 7) := by
  change Observation _ _ _ comparison.type _ _; rw [comparisonType]; exact .integer 7
private theorem outerKey : KeyRep outerCertificate signatures (fun _ _ => False) (.integer 9) (.integer 9) := by
  change Observation _ _ _ comparison.type _ _; rw [comparisonType]; exact .integer 9
private def keys : List Value := [.integer 9, .integer 7]
private def outerEmpty : Value := Core.OrderedMapping.encode outerLayout []
private def innerEmpty : Value := Core.OrderedMapping.encode innerLayout []
private def source : Dynamic.Value := .mapping .integer innerType []
private def projections : List Dynamic.EvaluatedProjection := [.index (.integer 9), .index (.integer 7)]
private theorem innerFault : DataPlaceFaultTree.Tree checked signatures (fun _ _ => False) prepared keys
    (.mapping .integer functionType []) innerEmpty innerLayout.type [.index innerIndex] [.index (.integer 7)]
    (.missingMappingDefault functionType) Word.zero 3 :=
  .missing (valueRelation := fun _ _ => False) innerCertificate innerKey (.integer 7) rfl .nil .nil (by intro impossible; cases impossible)
private theorem fault : DataPlaceFaultTree.Tree checked signatures (fun _ _ => False) prepared keys
    source outerEmpty outerLayout.type prepared.steps projections (.missingMappingDefault functionType) Word.zero 6 := by
  apply DataPlaceFaultTree.Tree.mapping (count := 3) (valueRelation := fun _ _ => False)
    outerCertificate outerKey (.integer 9) rfl .nil (.default .nil (.mapping _ _))
  intro value represented
  rcases represented with impossible | ⟨_, tree⟩
  · contradiction
  · cases tree with
    | mapping key value id selected =>
      change some ⟨0⟩ = some id at selected
      cases selected
      exact innerFault

/-- Even a malformed replacement expression cannot be reached after the
independent source fault. Only the two lookup initializers allocate cells. -/
example : ∃ finalStore administrative,
    Dynamic.ProjectionsFaults (some source) projections (.missingMappingDefault functionType) ∧
    Evaluates [outerEmpty, packValues keys] [.integer 900]
      (select prepared prepared.steps (.var 0) (.var 1)) (.inLeft prepared.optionalLeaf (.word Word.zero)) finalStore ∧
    Evaluates [outerEmpty, packValues keys] [.integer 900]
      (update prepared prepared.steps outerLayout.type (.var 0) (.var 1) (.apply .unit .unit))
      (.inLeft outerLayout.type (.word Word.zero)) finalStore ∧
    finalStore = [.integer 900] ++ administrative ∧ administrative.length = 6 :=
  fault.preserves noIdentities rfl [outerEmpty, packValues keys] [.integer 900] (.var 0) (.var 1) (.apply .unit .unit) (.var rfl) (.var rfl)

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)
def run : IO Unit := do
  let prepared ← match prepare checked 20 route Word.zero (fun _ => Word.zero) with
    | .ok value => pure value
    | .error error => throw (IO.userError s!"nested-fault preparation failed: {reprStr error}")
  let keyType : Core.Ty := .product .integer .integer
  let replacement : Value := .pair (.inLeft .word .unit) (.closure .unit (.sum .word .unit) (.inRight .word .unit) [])
  for write in [false, true] do
    let helper := if write then setter prepared keyType else getter prepared keyType
    let argument := if write then .pair (.inLeft outerLayout.type .unit) (.pair (packValues keys) replacement)
      else .pair (.inLeft outerLayout.type .unit) (packValues keys)
    let argumentType := if write then .product (.sum .unit outerLayout.type) (.product keyType innerLayout.valueType)
      else .product (.sum .unit outerLayout.type) keyType
    let resultType := if write then outerLayout.type else .sum .unit innerLayout.valueType
    let expression := .apply helper (.var 0)
    assertTrue (infer? [argumentType] expression catalog.definitions == some (.sum .word resultType)) "nested fault helper failed checker"
    let initial := Core.State.initial expression [argument] [.integer 900]
    let check := fun result => do
      match result with
      | .done value store =>
        assertTrue (value == .inLeft resultType (.word Word.zero)) "nested fault did not retain exact language reason"
        assertTrue (store.length == 7) "nested fault ran insertion or lost lookup helpers"
        assertTrue (store[0]? == some (.integer 900)) "nested fault wrote the source prefix"
      | other => throw (IO.userError s!"nested fault became machine failure or exhaustion: {reprStr other}")
    check (runStateful 10000 initial)
    match runStateful 9 initial with
    | .outOfFuel checkpoint => check (runStateful 10000 checkpoint)
    | other => throw (IO.userError s!"nested fault expected checkpoint: {reprStr other}")
  IO.println "source Core nested path faults GREEN"

end Tests.SourceCoreDataPlacePathFaults
end

section
-- leanmerge: from Solcore.Test.SourceCoreDataPlacePaths
/-! A mixed mapping/member/mapping path. The actual preparation and checker
are used; source constructor metadata is authenticated independently. -/
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000
namespace Tests.SourceCoreDataPlacePaths
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open SourceCoreDataPlaces DataPlaceMappingIndex DataEquality DataEqualityValues DataPatternValues
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"place_paths", by decide⟩], by decide⟩⟩
private def dataId : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 1⟩
private def keyId (index : Nat) : ExpressionId := ⟨⟨owner, index⟩⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "place_paths.solc"⟩, 0, 1⟩
private def boxType : TypeSystem.Ty := .nominal dataId []
private def innerType : TypeSystem.Ty := .mapping .integer .integer
private def innerLayout : Core.OrderedMapping.Layout := ⟨.integer, .integer, ⟨0⟩⟩
private def outerLayout : Core.OrderedMapping.Layout := ⟨.integer, .namedData ⟨1⟩, ⟨2⟩⟩
private def signature : ProgramDataSignature := {
  id := dataId, name := "Box", parameters := []
  constructors := [⟨⟨dataId, 0⟩, "Box", [innerType, .integer], ⟨span, ⟨[], ⟨span, "Box"⟩, none⟩⟩⟩]
  source := ⟨span, ⟨none, ⟨span, "Box"⟩, none, span, []⟩⟩
}
private def signatures : ProgramSignatures := ⟨[], [], [], [], [signature], []⟩
private def catalog : SourceCoreDataCatalog.Catalog := { entries := [
  { sourceType := innerType, definition := some innerLayout.definition },
  { sourceType := boxType, definition := some ⟨[.product innerLayout.type .integer]⟩, constructors := [⟨dataId, 0⟩] },
  { sourceType := .mapping .integer boxType, definition := some outerLayout.definition }]
}
private def checked : SourceCoreDataCatalog.Checked := ⟨catalog, Core.DataEnvironment.isWellFormed_sound (by decide)⟩
private def metadata : DataConstructorInstantiation := ⟨⟨dataId, 0⟩, [], [innerType, .integer], boxType⟩
private def branch : MemberBranch := ⟨⟨⟨1⟩, 0⟩, [innerLayout.type, .integer]⟩
private def route : Route := ⟨.mapping .integer boxType, outerLayout.type, .integer,
  [.index outerLayout (keyId 0) boxType, .member ⟨1⟩ 0 [branch] innerLayout.type, .index innerLayout (keyId 1) .integer], some outerLayout⟩

private theorem except_get {α ε : Type} (result : Except ε α) (positive : result.toOption.isSome = true) :
    result = .ok (result.toOption.get positive) := by
  cases result with
  | error => simp [Except.toOption] at positive
  | ok value => rfl
private theorem comparisonExists : (SourceCoreDataEquality.prepare 20 checked .integer).toOption.isSome = true := by cbv
private def comparison := (SourceCoreDataEquality.prepare 20 checked .integer).toOption.get comparisonExists
private theorem comparisonGenerated : SourceCoreDataEquality.prepare 20 checked .integer = .ok comparison := except_get _ comparisonExists
private theorem scalarDefaultExists : (SourceCoreDefaultValue.prepare (TypeSystem.Ty.integer.size + 1) checked .integer).toOption.isSome = true := by decide
private def scalarDefault := (SourceCoreDefaultValue.prepare (TypeSystem.Ty.integer.size + 1) checked .integer).toOption.get scalarDefaultExists
private theorem scalarDefaultGenerated : SourceCoreDefaultValue.prepare (TypeSystem.Ty.integer.size + 1) checked .integer = .ok scalarDefault := except_get _ scalarDefaultExists
private theorem boxDefaultExists : (SourceCoreDefaultValue.prepare (boxType.size + 1) checked boxType).toOption.isSome = true := by decide
private def boxDefault := (SourceCoreDefaultValue.prepare (boxType.size + 1) checked boxType).toOption.get boxDefaultExists
private theorem boxDefaultGenerated : SourceCoreDefaultValue.prepare (boxType.size + 1) checked boxType = .ok boxDefault := except_get _ boxDefaultExists
private def innerIndex : PreparedIndex := ⟨innerLayout, keyId 1, 1, comparison.expression, scalarDefault.expression, Word.zero⟩
private def outerIndex : PreparedIndex := ⟨outerLayout, keyId 0, 0, comparison.expression, boxDefault.expression, Word.zero⟩
private def prepared : Prepared := ⟨route, [.index outerIndex, .member ⟨1⟩ 0 [branch] innerLayout.type, .index innerIndex],
  [(keyId 0, .integer), (keyId 1, .integer)], Word.zero⟩
private def innerCertificate : Index checked .integer innerIndex :=
  Index.of_generated comparisonGenerated scalarDefaultGenerated rfl rfl
private def outerCertificate : Index checked boxType outerIndex :=
  Index.of_generated comparisonGenerated boxDefaultGenerated rfl (by rfl)
private theorem accepted : prepare checked 20 route Word.zero (fun _ => Word.zero) = .ok prepared := by
  have inner : checked.catalog.entries[0]? = some ⟨innerType, some innerLayout.definition, []⟩ := rfl
  have outer : checked.catalog.entries[2]? = some ⟨.mapping .integer boxType, some outerLayout.definition, []⟩ := rfl
  simp [prepare, route, innerLayout, outerLayout, inner, outer, innerType,
    comparisonGenerated, scalarDefaultGenerated, boxDefaultGenerated,
    prepared, innerIndex, outerIndex, bind, Except.bind, pure, Except.pure, Except.mapError]

private theorem noIdentities : IdentityFaithful (fun _ _ => False) := by
  constructor <;> intros <;> contradiction
private theorem comparisonType : comparison.type = .integer := by
  have projection := comparison.projection
  rw [DataPlaceMappingPreparation.comparison_sourceType comparisonGenerated] at projection
  exact Except.ok.inj projection.symm
private abbrev IntegerRep := DataPatternTypedValues.TypedValueRep catalog signatures .integer
private abbrev Key := Observation catalog signatures (fun _ _ => False) .integer
private def innerSources (n : Int) : List (Dynamic.Value × Dynamic.Value) := [(.integer 7, .integer n), (.integer 7, .integer 22)]
private def innerEntries (n : Int) : Core.OrderedMapping.Entries := [(.integer 7, .integer n), (.integer 7, .integer 22)]
private def innerValue (n : Int) : Value := Core.OrderedMapping.encode innerLayout (innerEntries n)
private def boxSource (n : Int) : Dynamic.Value := .constructed metadata [.mapping .integer .integer (innerSources n), .integer 999]
private def boxValue (n : Int) : Value := .constructed ⟨⟨1⟩, 0⟩ (.pair (innerValue n) (.integer 999))
private inductive BoxRep : Dynamic.Value → Value → Prop where
  | intro (n : Int) : BoxRep (boxSource n) (boxValue n)
private def outerSources (n : Int) : List (Dynamic.Value × Dynamic.Value) := [(.integer 9, boxSource n)]
private def outerEntries (n : Int) : Core.OrderedMapping.Entries := [(.integer 9, boxValue n)]
private def outerSource (n : Int) : Dynamic.Value := .mapping .integer boxType (outerSources n)
private def outerValue (n : Int) : Value := Core.OrderedMapping.encode outerLayout (outerEntries n)
private def keys : List Value := [.integer 9, .integer 7]
private def projections : List Dynamic.EvaluatedProjection := [.index (.integer 9), .member "entries" 0, .index (.integer 7)]
private def innerStep : List PreparedStep := [.index innerIndex]
private def mixedSteps : List PreparedStep := [.index outerIndex, .member ⟨1⟩ 0 [branch] innerLayout.type, .index innerIndex]
private theorem innerKey (n : Int) : KeyRep innerCertificate signatures (fun _ _ => False) (.integer n) (.integer n) := by
  change Observation _ _ _ comparison.type _ _
  rw [comparisonType]; exact .integer n
private theorem outerKey (n : Int) : KeyRep outerCertificate signatures (fun _ _ => False) (.integer n) (.integer n) := by
  change Observation _ _ _ comparison.type _ _
  rw [comparisonType]; exact .integer n
private theorem innerRelated (n : Int) :
    OrderedMapping.EntriesRel (KeyRep innerCertificate signatures (fun _ _ => False)) IntegerRep (innerSources n) (innerEntries n) :=
  .cons (innerKey 7) (.integer n) (.cons (innerKey 7) (.integer 22) .nil)
private theorem outerRelated (n : Int) :
    OrderedMapping.EntriesRel (KeyRep outerCertificate signatures (fun _ _ => False)) BoxRep (outerSources n) (outerEntries n) :=
  .cons (outerKey 9) (.intro n) .nil
private theorem boxAuthenticated : checked.catalog.resolveConstructor signatures metadata = .ok ⟨⟨1⟩, 0⟩ := by cbv

private theorem readInner : DataPlaceReadTree.Tree checked signatures (fun _ _ => False) prepared keys IntegerRep
    (.mapping .integer .integer (innerSources 11)) (innerValue 11) innerStep [.index (.integer 7)] (.integer 11) 4 := by
  apply DataPlaceReadTree.Tree.mapping (count := 0) innerCertificate (innerKey 7) rfl (innerRelated 11) (.found (.head ⟨rfl, .integer 7⟩))
  intro value represented
  rcases represented with represented | ⟨_, tree⟩
  · exact .leaf represented
  · cases tree
private theorem readBox : DataPlaceReadTree.Tree checked signatures (fun _ _ => False) prepared keys IntegerRep
    (boxSource 11) (boxValue 11) (.member ⟨1⟩ 0 [branch] innerLayout.type :: innerStep)
    [.member "entries" 0, .index (.integer 7)] (.integer 11) 4 :=
  .member (branch := branch) (values := [innerValue 11, .integer 999])
    (sources := [.mapping .integer .integer (innerSources 11), .integer 999])
    boxAuthenticated rfl rfl rfl rfl rfl .head rfl readInner
private theorem readOuter : DataPlaceReadTree.Tree checked signatures (fun _ _ => False) prepared keys IntegerRep
    (outerSource 11) (outerValue 11) mixedSteps projections (.integer 11) 8 := by
  apply DataPlaceReadTree.Tree.mapping (count := 4) outerCertificate (outerKey 9) rfl (outerRelated 11) (.found (.head ⟨rfl, .integer 9⟩))
  intro value represented
  rcases represented with represented | ⟨_, tree⟩
  · cases represented; exact readBox
  · have impossible := tree.meaning.defaultable
    cases impossible

example : ∃ finalStore administrative,
    Dynamic.ProjectionsRead (some (outerSource 11)) projections (some (.integer 11)) ∧
    Evaluates [outerValue 11, packValues keys] [.integer 900]
      (select prepared mixedSteps (.var 0) (.var 1)) (.inRight .word (.inRight .unit (.integer 11))) finalStore ∧
    finalStore = [.integer 900] ++ administrative ∧ administrative.length = 8 := by
  obtain ⟨leaf, finalStore, administrative, sourceRead, represented, evaluated, extended, counted⟩ :=
    readOuter.preserves noIdentities rfl [outerValue 11, packValues keys] [.integer 900] (.var 0) (.var 1) (.var rfl) (.var rfl)
  cases represented
  exact ⟨finalStore, administrative, sourceRead, evaluated, extended, counted⟩

private theorem integerKey_cases {source : Dynamic.Value} {value : Value}
    (represented : KeyRep innerCertificate signatures (fun _ _ => False) source value) : Key source value := by
  change Observation _ _ _ comparison.type _ _ at represented
  rwa [comparisonType] at represented
private theorem innerUnique (n : Int) {value : Value}
    (represented : OrderedMapping.ValueRel innerLayout (KeyRep innerCertificate signatures (fun _ _ => False)) IntegerRep (innerSources n) value) :
    value = innerValue n := by
  obtain ⟨entries, related, rfl⟩ := represented
  cases related with
  | cons key first rest =>
    have key := integerKey_cases key
    cases key
    cases first
    cases rest with
    | cons key second tail =>
      have key := integerKey_cases key
      cases key
      cases second
      cases tail
      rfl
private abbrev InnerRep : OrderedMapping.Relation := fun source value =>
  ∃ n, source = .mapping .integer .integer (innerSources n) ∧ value = innerValue n

private theorem updateInner : DataPlaceUpdateTree.Tree checked signatures (fun _ _ => False) prepared keys
    (.integer 55) (.integer 55) InnerRep (.mapping .integer .integer (innerSources 11)) (innerValue 11)
    innerStep [.index (.integer 7)] (.mapping .integer .integer (innerSources 55)) 8 := by
  apply DataPlaceUpdateTree.Tree.mapping (count := 0) innerCertificate (innerKey 7) rfl (innerRelated 11) (.found (.head ⟨rfl, .integer 7⟩))
    (updatedChild := .integer 55)
  · intro value _; exact .leaf (.integer 55)
  · exact .update (.head ⟨rfl, .integer 7⟩)
  · intro value represented; exact ⟨55, rfl, innerUnique 55 represented⟩
private theorem updateBox : DataPlaceUpdateTree.Tree checked signatures (fun _ _ => False) prepared keys
    (.integer 55) (.integer 55) BoxRep (boxSource 11) (boxValue 11)
    (.member ⟨1⟩ 0 [branch] innerLayout.type :: innerStep) [.member "entries" 0, .index (.integer 7)] (boxSource 55) 8 := by
  apply DataPlaceUpdateTree.Tree.member (branch := branch) (values := [innerValue 11, .integer 999])
    (sources := [.mapping .integer .integer (innerSources 11), .integer 999]) boxAuthenticated rfl rfl rfl rfl rfl .head rfl updateInner
  intro child represented
  obtain ⟨n, same, rfl⟩ := represented
  have sameN : n = 55 := by cases same; rfl
  subst n
  exact .intro 55
private abbrev OuterRep : OrderedMapping.Relation := fun source value =>
  ∃ n, source = outerSource n ∧ value = outerValue n
private theorem updateOuter : DataPlaceUpdateTree.Tree checked signatures (fun _ _ => False) prepared keys
    (.integer 55) (.integer 55) OuterRep (outerSource 11) (outerValue 11) mixedSteps projections (outerSource 55) 16 := by
  apply DataPlaceUpdateTree.Tree.mapping (count := 8) outerCertificate (outerKey 9) rfl (outerRelated 11) (.found (.head ⟨rfl, .integer 9⟩))
    (updatedChild := boxSource 55)
  · intro value represented
    rcases represented with represented | ⟨_, tree⟩
    · cases represented; exact updateBox
    · have impossible := tree.meaning.defaultable; cases impossible
  · exact .update (.head ⟨rfl, .integer 9⟩)
  · intro value represented
    obtain ⟨entries, related, rfl⟩ := represented
    cases related with
    | cons key boxed tail =>
      change Observation _ _ _ comparison.type _ _ at key
      rw [comparisonType] at key
      cases key
      cases boxed
      cases tail
      exact ⟨55, rfl, rfl⟩

example : ∃ finalStore administrative,
    Dynamic.ProjectionsUpdate (fun _ value => value = .integer 55) (some (outerSource 11)) projections (outerSource 55) ∧
    Evaluates [outerValue 11, packValues keys, .integer 55] [.integer 900]
      (update prepared mixedSteps outerLayout.type (.var 0) (.var 1) (.var 2)) (.inRight .word (outerValue 55)) finalStore ∧
    finalStore = [.integer 900] ++ administrative ∧ administrative.length = 16 := by
  obtain ⟨value, finalStore, administrative, sourceUpdate, represented, evaluated, extended, counted⟩ :=
    updateOuter.preserves noIdentities rfl [outerValue 11, packValues keys, .integer 55] [.integer 900]
      outerLayout.type (.var 0) (.var 1) (.var 2) (.var rfl) (.var rfl) (.var rfl)
  obtain ⟨n, same, rfl⟩ := represented
  have sameN : n = 55 := by cases same; rfl
  subst n
  exact ⟨finalStore, administrative, sourceUpdate, evaluated, extended, counted⟩

example : ∃ finalStore administrative, administrative.length = 16 ∧ finalStore = [.integer 900] ++ administrative ∧
    ∃ required, ∀ fuel, required ≤ fuel → runStateful fuel
      (.initial (.apply (setter prepared (.product .integer .integer)) (.var 0))
        [.pair (.inRight .unit (outerValue 11)) (.pair (packValues keys) (.integer 55))] [.integer 900]) =
      .done (.inRight .word (outerValue 55)) finalStore := by
  obtain ⟨value, finalStore, administrative, _, _, represented, evaluated, extended, counted⟩ :=
    DataPlacePathHelpers.setter_preserves (.initialized (.mapping .integer boxType) _ _) updateOuter rfl noIdentities rfl
      [.pair (.inRight .unit (outerValue 11)) (.pair (packValues keys) (.integer 55))] [.integer 900]
      (.product .integer .integer) (.var 0) (.var rfl)
  obtain ⟨n, same, rfl⟩ := represented
  have sameN : n = 55 := by cases same; rfl
  subst n
  exact ⟨finalStore, administrative, counted, extended, evaluation_runStateful_complete_with_sufficient_fuel evaluated⟩

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)
private def checkRun (expression : Expr) (environment : Environment) (context : Core.Context) (initial : Store)
    (resultType : Core.Ty) (expected : Value) (expectedPrefix : Store) (allocated : Nat) : IO Unit := do
  assertTrue (infer? context expression catalog.definitions == some resultType) "mixed path code failed Core checker"
  let check := fun result => do
    match result with
    | .done value store =>
      assertTrue (value == expected) "mixed path returned wrong value or sibling contents"
      assertTrue (store.length == initial.length + allocated) "mixed path helper cell count differs"
      assertTrue (store.take expectedPrefix.length == expectedPrefix) "mixed path changed wrong store prefix"
    | other => throw (IO.userError s!"mixed path did not complete: {reprStr other}")
  let state := Core.State.initial expression environment initial
  check (runStateful 20000 state)
  match runStateful 19 state with
  | .outOfFuel checkpoint => check (runStateful 20000 checkpoint)
  | other => throw (IO.userError s!"mixed path expected checkpoint: {reprStr other}")
private def boxExpression (n sibling : Int) : Expr :=
  .construct ⟨⟨1⟩, 0⟩ (.pair
    (Core.OrderedMapping.cons innerLayout (.integer 7) (.integer n)
      (Core.OrderedMapping.cons innerLayout (.integer 7) (.integer 22) (Core.OrderedMapping.empty innerLayout)))
    (.integer sibling))
private def outerExpression (n sibling : Int) : Expr :=
  Core.OrderedMapping.cons outerLayout (.integer 9) (boxExpression n sibling) (Core.OrderedMapping.empty outerLayout)
private def latestValue (n sibling : Int) : Value :=
  Core.OrderedMapping.encode outerLayout [(.integer 9, .constructed ⟨⟨1⟩, 0⟩ (.pair (innerValue n) (.integer sibling)))]
private def event (digit value : Int) : Expr :=
  .letE (.storeCell (.var 1) (.binary .integerAdd (.binary .integerMul (.loadCell (.var 1)) (.integer 10)) (.integer digit)))
    (LanguageResult.success (.integer value))

def run : IO Unit := do
  let prepared ← match prepare checked 20 route Word.zero (fun _ => Word.zero) with
    | .ok value => pure value
    | .error error => throw (IO.userError s!"mixed route preparation failed: {reprStr error}")
  let keyType : Core.Ty := .product .integer .integer
  let readArgument : Value := .pair (.inRight .unit (outerValue 11)) (packValues keys)
  checkRun (.apply (getter prepared keyType) (.var 0)) [readArgument]
    [.product (.sum .unit outerLayout.type) keyType] [.integer 900]
    (.sum .word (.sum .unit .integer)) (.inRight .word (.inRight .unit (.integer 11))) [.integer 900] 8
  let writeArgument : Value := .pair (.inRight .unit (outerValue 11)) (.pair (packValues keys) (.integer 55))
  checkRun (.apply (setter prepared keyType) (.var 0)) [writeArgument]
    [.product (.sum .unit outerLayout.type) (.product keyType .integer)] [.integer 900]
    (.sum .word outerLayout.type) (.inRight .word (outerValue 55)) [.integer 900] 16
  -- Events 1 and 2 are the two index evaluations. Event 3 is the RHS.
  -- The RHS changes both the selected value and a sibling in the latest root.
  let keyCode := SourceCoreCalls.packArguments [⟨.integer, event 1 9⟩, ⟨.integer, event 2 7⟩]
  let rhs := .letE (.storeCell (.var 0) (.inRight .unit (outerExpression 22 777))) ((event 3 5).weakenAt 0)
  let next := LanguageResult.success (.pair (.loadCell (.var 0)) (.loadCell (.var 1)))
  let outputType := .product (.sum .unit outerLayout.type) .integer
  let expression := execute prepared (.var 0) keyCode rhs next outputType (some .integerAdd) false Word.zero
  let initial : Store := [.inRight .unit (outerValue 11), .integer 0]
  let finalPrefix : Store := [.inRight .unit (latestValue 16 777), .integer 123]
  checkRun expression [.cellRef (.sum .unit outerLayout.type) 0, .cellRef .integer 1]
    [.cell (.sum .unit outerLayout.type), .cell .integer] initial (.sum .word outputType)
    (.inRight .word (.pair (.inRight .unit (latestValue 16 777)) (.integer 123))) finalPrefix 24
  IO.println "source Core mixed path certificates GREEN"

end Tests.SourceCoreDataPlacePaths
end

section
-- leanmerge: from Solcore.Test.SourceCoreDataPlaceRhsReflection
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
end

section
-- leanmerge: from Solcore.Test.SourceCoreDataPlaceSetterReflection
/-! Live-root reconstruction retains a sibling changed before setter execution.
Reflection constructs the independent source update from actual generated Core
execution and authentic full payloads. The setter itself leaves the cell intact;
only the enclosing assignment's later storeCell may commit this value. -/
set_option autoImplicit false
set_option maxRecDepth 16384
namespace Tests.SourceCoreDataPlaceSetterReflection
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open SourceCoreDataPlaces DataPayload DataPlaceRouteCertificates

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"setter_reflection", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def dataId : Resolved.DeclarationId := ⟨moduleId, 1⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "setter_reflection.solc"⟩, 0, 1⟩
private def boxType : TypeSystem.Ty := .nominal dataId []
private def signature : ProgramDataSignature := {
  id := dataId, name := "Box", parameters := []
  constructors := [⟨⟨dataId, 0⟩, "Box", [.bool, .bool], ⟨span, ⟨[], ⟨span, "Box"⟩, none⟩⟩⟩]
  source := ⟨span, ⟨none, ⟨span, "Box"⟩, none, span, []⟩⟩ }
private def signatures : ProgramSignatures := ⟨[], [], [], [], [signature], []⟩
private def catalog : SourceCoreDataCatalog.Catalog := { entries := [
  { sourceType := boxType, definition := some ⟨[.product .bool .bool]⟩, constructors := [⟨dataId, 0⟩] }] }
private def checked : SourceCoreDataCatalog.Checked := ⟨catalog, DataEnvironment.isWellFormed_sound (by decide)⟩
private def binder : TypedBinder := ⟨⟨owner, 0⟩, "root", .mono boxType, [], false, none⟩
private def source : TypedSource := { owner, inputs := [binder], roots := [], nodes := [] }
private def functions : GenericHeap.PayloadModel catalog where
  Represents := fun _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  extend := fun impossible _ _ => False.elim impossible
private def model := payloadModel catalog signatures functions
private theorem functionTypes : FunctionRuntimeTypes functions := fun impossible => False.elim impossible
private theorem observations : FunctionObservations catalog signatures functions (fun _ _ => False) := fun impossible => False.elim impossible
private theorem faithful : DataEquality.IdentityFaithful (fun _ _ => False) := by constructor <;> intros <;> contradiction
private theorem layouts : CatalogLayouts catalog := by
  apply CatalogLayouts.of_entries
  intro id entry selected
  rcases id with ⟨index⟩
  cases index with
  | zero => cases selected; trivial
  | succ index => simp [catalog] at selected
private def branches : List MemberBranch := [⟨⟨⟨0⟩, 0⟩, [.bool, .bool]⟩]
private def route : Route := ⟨boxType, .namedData ⟨0⟩, .bool, [.member ⟨0⟩ 0 branches .bool], none⟩
private def invalid : Word := ⟨23, by decide⟩
private def prepared : Prepared := ⟨route, [.member ⟨0⟩ 0 branches .bool], [], invalid⟩
private theorem preparedBy : prepare checked 5 route invalid (fun _ => Word.zero) = .ok prepared := by cbv
private def projections : List PlaceProjection := [.member "value" 0]
private theorem profile : Profile signatures source boxType projections .bool := by
  refine .member (field := .bool) (signature := signature) (arguments := []) rfl (by cbv) ?_ (.nil rfl)
  intro constructor member
  simp only [signature, List.mem_cons, List.not_mem_nil, or_false] at member
  subst constructor
  rfl
private theorem raw : RawPath checked signatures source boxType (.namedData ⟨0⟩) route.steps projections .bool .bool [] := by
  obtain ⟨_, types, raw⟩ := raw_of_routeSteps profile (show catalog.project boxType = .ok (.namedData ⟨0⟩) by rfl)
    (show catalog.project TypeSystem.Ty.bool = .ok .bool by rfl)
    (show routeSteps checked signatures source (.binder binder.id) binder.id boxType projections = .ok (route.steps, TypeSystem.Ty.bool) by cbv)
  have keys : DataExpressionSequence.Tree source (fun _ _ _ => True) [] [] [] [] := .nil
  have same := raw.keyTypes.tree_types keys
  rw [← same] at raw
  exact raw
private def metadata : DataConstructorInstantiation := ⟨⟨dataId, 0⟩, [], [.bool, .bool], boxType⟩
private def sourceRoot : Dynamic.Value := .constructed metadata [.bool true, .bool false]
private def coreRoot : Value := .constructed ⟨⟨0⟩, 0⟩ (.pair (.bool true) (.bool false))
private theorem rootRelated {mapping : GeneralHeap.LocationMap} {world : StoreTyping} :
    ValueRep catalog signatures functions mapping world boxType sourceRoot coreRoot (.namedData ⟨0⟩) :=
  .constructed (metadata := metadata) (tag := ⟨⟨0⟩, 0⟩) (declaration := dataId) (arguments := [])
    rfl rfl (by cbv) rfl rfl (.cons (.bool true) (.cons (.bool false) .nil))
private def cell : Dynamic.Cell := ⟨boxType, some sourceRoot, none⟩
private def heap : Dynamic.Heap := ⟨[cell]⟩
private def world : StoreTyping := [OptionalCell.cellType (.namedData ⟨0⟩), .integer]
private def store : Store := [.inRight .unit coreRoot, .integer 900]
private def environment : Environment := [.cellRef (OptionalCell.cellType (.namedData ⟨0⟩)) 0, .unit, .bool false]
private def context : Core.Context := [OptionalCell.referenceType (.namedData ⟨0⟩), .unit, .bool]
private theorem heapRelated : GenericHeap.HeapRepresents model [0] world heap store := by
  have empty : GenericHeap.HeapRepresents model [] [] ⟨[]⟩ [] := .empty
  exact (empty.allocate (.initialized rootRelated) .append).1.allocate_administrative .integer
private theorem environmentTyped : RuntimeEnvironmentHasTypes world environment context catalog.definitions :=
  .cons (.cellRef rfl) (.cons .unit (.cons .bool .nil))
private theorem nonMapping : ¬ ∃ key value, boxType = .mapping key value := by
  intro impossible; obtain ⟨_, _, same⟩ := impossible; cases same
private theorem rootLayout : DataPlaceSnapshot.RootLayout catalog prepared boxType := .ordinary nonMapping rfl
private def expression : Expr := .apply (setter prepared .unit) (.pair (.loadCell (.var 0)) (.pair (.var 1) (.var 2)))
private def updatedSource : Dynamic.Value := .constructed metadata [.bool false, .bool false]
private def updatedCore : Value := .constructed ⟨⟨0⟩, 0⟩ (.pair (.bool false) (.bool false))
private theorem expectedChange : Dynamic.ProjectionsUpdate (fun _ value => value = .bool false)
    (some sourceRoot) [.member "value" 0] updatedSource := .member .head (.leaf rfl) .head
private theorem ran : runStateful 100 (.initial expression environment store) = .done (.inRight .word updatedCore) store := by cbv

/-- The second field is taken from the latest root and survives the first-field
replacement. No source update trace is supplied to the reflection theorem. -/
example : ∃ futureWorld administrative,
    ValueRep catalog signatures functions [0] futureWorld boxType updatedSource updatedCore (.namedData ⟨0⟩) ∧
    Dynamic.ProjectionsUpdate (fun _ value => value = .bool false) (some sourceRoot) [.member "value" 0] updatedSource ∧
    GenericHeap.HeapRepresents model [0] futureWorld heap store ∧
    GeneralHeap.AdministrativePreserved [0] store [0] store ∧ store = store ++ administrative := by
  obtain ⟨futureWorld, administrative, result, _, heaps, _, frame, appended⟩ :=
    DataPlaceSetterReflection.reflects_at functionTypes layouts observations faithful (cell := cell) raw
      (DataPlaceMappingPreparation.steps_of_prepare preparedBy).2.2 (.member .nil) .nil rfl rootLayout (.bool false)
      heapRelated ⟨rfl, rfl⟩ (.intro .head) environmentTyped (infer_sound (by cbv))
      (.var rfl) (.var (index := 1) rfl) (.var (index := 2) rfl) (runStateful_evaluation_sound ran)
  cases result with
  | updated root changed related =>
    cases root
    have same := changed.functional (fun _ _ _ left right => left.trans right.symm) expectedChange
    cases same
    exact ⟨futureWorld, administrative, related, changed, heaps, frame, appended⟩

/-- The source-only construction retains first-match duplicate position and
appends an absent key, using the language's own MappingLookup/Absent rules. -/
example : ∃ updated, Dynamic.ProjectionsUpdate (fun _ value => value = .bool false)
    (some (.mapping .bool .bool [(.bool true, .bool true), (.bool true, .bool true)])) [.index (.bool true)] updated :=
  DataPlaceUpdateTotality.read_update (.indexFound (.head ⟨rfl, .bool true⟩) .nil) (.bool false)

example : ∃ updated, Dynamic.ProjectionsUpdate (fun _ value => value = .bool true)
    (some (.mapping .bool .bool [])) [.index (.bool false)] updated :=
  DataPlaceUpdateTotality.read_update (.indexDefault .nil .bool .nil) (.bool true)

end Tests.SourceCoreDataPlaceSetterReflection
end

section
-- leanmerge: from Solcore.Test.SourceCoreDataPlaceWriteBack
/-! A commit consumer preserves an unmapped administrative cell and two
references to the same mapped source location. The source snapshot may precede
the latest cell, which is the one reconstructed and written. -/
set_option autoImplicit false
namespace Tests.SourceCoreDataPlaceWriteBack
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open SourceCoreDataPlaces GeneralHeap GenericHeap DataEquality
private def catalog : SourceCoreDataCatalog.Catalog := {}
private def checked : SourceCoreDataCatalog.Checked := ⟨catalog, Core.DataEnvironment.isWellFormed_sound (by decide)⟩
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def model := finitePayload catalog signatures
private def prepared : Prepared := ⟨⟨.integer, .integer, .integer, [], none⟩, [], [], Word.zero⟩
private def cell : Dynamic.Cell := ⟨.integer, some (.integer 7), none⟩
private def heap : Dynamic.Heap := ⟨[cell]⟩
private def world : StoreTyping := [.sum .unit .integer, .integer]
private def store : Store := [.inRight .unit (.integer 7), .integer 900]
private def argument : Value := .pair (.inRight .unit (.integer 7)) (.pair .unit (.integer 55))
private def environment : Environment := [.cellRef (.sum .unit .integer) 0, .cellRef (.sum .unit .integer) 0, argument]
private def context : Core.Context := [.cell (.sum .unit .integer), .cell (.sum .unit .integer),
  .product (.sum .unit .integer) (.product .unit .integer)]
private theorem related : HeapRepresents model [0] world heap store := by
  have empty : HeapRepresents model [] [] ⟨[]⟩ [] := .empty
  have represented : model.Represents [] [] .integer (.integer 7) (.integer 7) .integer := ⟨rfl, .integer 7⟩
  exact (empty.allocate (.initialized represented) .append).1.allocate_administrative .integer
private theorem environmentTyped : RuntimeEnvironmentHasTypes world environment context catalog.definitions :=
  .cons (.cellRef rfl) (.cons (.cellRef rfl) (.cons (.pair (.inRight .integer) (.pair .unit .integer)) .nil))
private theorem faithful : IdentityFaithful (fun _ _ => False) := by constructor <;> intros <;> contradiction
private def expression : Expr := DataPlaceWriteBack.commit prepared .unit (.var 0) (.var 2)

example : ∃ updatedValue finalHeap finalStore futureWorld,
    Dynamic.ResolvedPlaceWrites (fun _ value => value = .integer 55) heap
      ⟨⟨0⟩, .integer, .integer, [], some (.integer 3)⟩ (.integer 55) finalHeap ∧
    Evaluates environment store expression (.inRight .word .unit) finalStore ∧
    WorldExtends world futureWorld ∧ HeapRepresents model [0] futureWorld finalHeap finalStore ∧
    model.Represents [0] futureWorld .integer (.integer 55) updatedValue .integer ∧
    finalStore.read? 0 = some (.inRight .unit updatedValue) ∧ AdministrativePreserved [0] store [0] finalStore := by
  have tree : DataPlaceUpdateTree.Tree checked signatures (fun _ _ => False) prepared []
      (.integer 55) (.integer 55) (fun source value => model.Represents [0] world cell.type source value .integer)
      (.integer 7) (.integer 7) [] [] (.integer 55) 0 := .leaf ⟨rfl, .integer 55⟩
  exact DataPlaceWriteBack.commit_preserves related ⟨rfl, rfl⟩ (.intro .head) rfl
    (.initialized .integer (.integer 7) (.integer 7)) tree rfl faithful rfl environmentTyped
    (infer_sound (by decide)) (.var rfl) (.var rfl) .integer (some (.integer 3))

private def observeAliases : Expr := .letE expression
  (LanguageResult.success (.pair (.loadCell (.var 1)) (.loadCell (.var 2))))
example : infer? context observeAliases = some (.sum .word (.product (.sum .unit .integer) (.sum .unit .integer))) := by
  simp [observeAliases, expression, DataPlaceWriteBack.commit, prepared, setter, LanguageResult.bind,
    LanguageResult.success, OptionalCell.cellType, LanguageResult.resultType, Expr.weakenAt]
  decide
example : runStateful 100 (.initial observeAliases environment store) =
    .done (.inRight .word (.pair (.inRight .unit (.integer 55)) (.inRight .unit (.integer 55))))
      [.inRight .unit (.integer 55), .integer 900] := by cbv

end Tests.SourceCoreDataPlaceWriteBack
end

section
-- leanmerge: from Solcore.Test.SourceCoreDataPlaces
#check_failure Solcore.Frontend.SourceTypedRuntime.run

set_option autoImplicit false

namespace Tests.SourceCoreDataPlaces

open Solcore Solcore.Frontend Solcore.Core

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)
private def w (value : Nat) : Core.Value := .word (Core.Word.ofNatModulo value)

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := []
  mainSources := [{ path := "main.solc", content := String.intercalate "\n" [
    "enum Tree { Leaf(Word), Pair(Tree, Tree) }",
    "function order() returns (Word) {",
    " let table: mapping(Word => Word); let calls: Word = 0;",
    " let key: function() returns (Word) = lam() -> Word { calls += 1; table[1] = 10; return 1; };",
    " let rhs: function() returns (Word) = lam() -> Word { table[1] = 100; table[2] = 50; return 3; };",
    " table[key()] += rhs(); return table[1] + table[2] + calls; }",
    "function nested() returns (Word) {",
    " let table: mapping(Word => mapping(Word => Word)); let calls: Word = 0;",
    " let first: function() returns (Word) = lam() -> Word { calls += 1; table[1][2] = 10; return 1; };",
    " let second: function() returns (Word) = lam() -> Word { calls += 1; table[1][2] = 20; return 2; };",
    " let rhs: function() returns (Word) = lam() -> Word { table[1][2] = 100; table[1][3] = 7; table[9][9] = 11; return 5; };",
    " table[first()][second()] += rhs(); return table[1][2] + table[1][3] + table[9][9] + calls; }",
    "function replaceLatest() returns (Word) {",
    " let table: mapping(Word => Word); table[1] = 10;",
    " let rhs: function() returns (Word) = lam() -> Word { let fresh: mapping(Word => Word); fresh[3] = 9; table = fresh; return 4; };",
    " table[1] += rhs(); return table[1] + table[3]; }",
    "function ordered(table: mapping(Word => Word)) returns (mapping(Word => Word)) { table[7] = 80; table[9] = 90; return table; }",
    "function unary() returns (Word) { let table: mapping(Word => Word); table[1] = 0; table[1] ~=; return table[1]; }",
    "function header() returns (Word) { let table: mapping(Word => Word); for (let i: Word = 0; i < 3; table[i] += 2, i += 1) { table[i] = i; } return table[0] + table[1] + table[2]; }",
    "function absentDefault() returns (Word) {",
    " let table: mapping(Word => Tree); let count: Word = 0;",
    " let key: function() returns (Word) = lam() -> Word { count += 17; return 1; };",
    " let rhs: function() returns (Tree) = lam() -> Tree { count += 111; return .Leaf(7); };",
    " table[key()] = rhs(); return count; }",
    "function rhsFailure() returns (Word) { let table: mapping(Word => Word); let missing: Word; table[1] += missing; return 0; }"
  ] }]
}

private def entryFor (program : CheckedProgram) (checked : SourceCoreDataCatalog.Checked) (name : String) :
    IO (SourceCoreGeneralEntry.Entry checked) := do
  let signature ← match program.signatures.functions.filter (·.name == name) with
    | [signature] => pure signature
    | _ => throw (IO.userError s!"place function missing: {name}")
  let plan ← match SourceSpecializationWorklist.run program
      [{ declaration := signature.id, parameterSubstitution := [] }] 256 with
    | .ok (.complete plan) => pure plan
    | result => throw (IO.userError s!"place specialization failed: {reprStr result}")
  match SourceCoreGeneralFunctions.prepareWithCatalog program plan checked 256 with
  | .ok prepared => match prepared.entries with
      | [entry] => pure entry
      | _ => throw (IO.userError "place seed count changed")
  | .error error => throw (IO.userError s!"{name} place compilation failed: {reprStr error}")

private def expect {checked : SourceCoreDataCatalog.Checked} (entry : SourceCoreGeneralEntry.Entry checked)
    (inputs : List Core.Value) (expected : Core.Value) : IO Unit := do
  match entry.run inputs 65536 with
  | .ok result => match result.observation with
      | .succeeded actual _ =>
        assertTrue (actual == expected) s!"place result changed: {reprStr actual}; expected {reprStr expected}"
      | other => throw (IO.userError s!"place run failed: {reprStr other}")
  | .error error => throw (IO.userError s!"place input rejected: {reprStr error}")

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error error => throw (IO.userError s!"place source rejected: {reprStr error}")
  let tree ← match program.signatures.dataTypes.filter (·.name == "Tree") with
    | [tree] => pure tree
    | _ => throw (IO.userError "place Tree missing")
  let treeType := TypeSystem.Ty.nominal tree.id []
  let checked ← match SourceCoreDataCatalog.prepare program.signatures 256
      [treeType, .mapping .word .word, .mapping .word (.mapping .word .word), .mapping .word treeType] with
    | .ok checked => pure checked
    | .error error => throw (IO.userError s!"place catalog rejected: {reprStr error}")
  -- Closures capture by value: the key and RHS closures assign only their
  -- call's copies of `table` and `calls`, so only the compound write reaches
  -- `table`, from its default 0.
  expect (← entryFor program checked "order") [] (w 3)
  let nested ← entryFor program checked "nested"
  expect nested [] (w 5)
  match nested.run [] 32 with
  | .ok result => match result.checkpoint? with
      | some checkpoint => match (checkpoint.resume 65536).observation with
          | .succeeded actual _ => assertTrue (actual == w 5) "place resume changed the compound result"
          | other => throw (IO.userError s!"place resume failed: {reprStr other}")
      | none => throw (IO.userError "place run did not suspend")
  | .error error => throw (IO.userError s!"place checkpoint rejected: {reprStr error}")
  -- The RHS replaces only its call's copy of `table`.
  expect (← entryFor program checked "replaceLatest") [] (w 14)
  let mapId ← match checked.catalog.identity? (.mapping .word .word) with
    | some identity => pure identity
    | none => throw (IO.userError "place mapping identity missing")
  let layout : Core.OrderedMapping.Layout := ⟨.word, .word, mapId⟩
  expect (← entryFor program checked "ordered")
    [Core.OrderedMapping.encode layout [(w 7, w 1), (w 7, w 2), (w 3, w 4)]]
    (Core.OrderedMapping.encode layout [(w 7, w 80), (w 7, w 2), (w 3, w 4), (w 9, w 90)])
  expect (← entryFor program checked "unary") [] (.word (Core.Word.bitNot (Core.Word.ofNatModulo 0)))
  expect (← entryFor program checked "header") [] (w 9)
  let failing ← entryFor program checked "absentDefault"
  let treeMap ← match checked.catalog.identity? (.mapping .word treeType) with
    | some identity => pure identity
    | none => throw (IO.userError "place Tree mapping identity missing")
  match failing.run [] 65536 with
  | .ok result => match result.observation with
      | .failed reason store => do
          match failing.failureDiagnostic? reason with
          | some diagnostic =>
            assertTrue
              (decide (diagnostic.error = .typeMismatch treeType none) && diagnostic.span.isSome)
              "place missing default lost its exact source diagnostic"
          | none => throw (IO.userError "place missing default lost diagnostic")
          -- The key's call copy of `count` holds 17; an RHS call would leave 111 in its own copy.
          assertTrue (store.contains (.inRight .unit (w 17)) && !store.contains (.inRight .unit (w 111)))
            "place selected after RHS or skipped key effects"
          assertTrue (store.contains (.inLeft (.namedData treeMap) .unit) &&
            !store.contains (.inRight .unit (.constructed ⟨treeMap, 0⟩ .unit)))
            "failed place resolution initialized the mapping root"
      | other => throw (IO.userError s!"place missing default result changed: {reprStr other}")
  | .error error => throw (IO.userError s!"place failing entry rejected: {reprStr error}")
  let rhsFailure ← entryFor program checked "rhsFailure"
  match rhsFailure.run [] 65536 with
  | .ok result => match result.observation with
      | .failed reason store => do
          match rhsFailure.failureDiagnostic? reason with
          | some diagnostic =>
            assertTrue (match diagnostic.error with | .uninitializedLocal _ => true | _ => false)
              "projected assignment replaced RHS failure with operand failure"
          | none => throw (IO.userError "projected RHS failure lost diagnostic")
          assertTrue (store.contains (.inLeft layout.type .unit) &&
            !store.contains (.inRight .unit (Core.OrderedMapping.encode layout [])))
            "RHS failure materialized an empty mapping"
      | other => throw (IO.userError s!"projected RHS failure changed: {reprStr other}")
  | .error error => throw (IO.userError s!"projected RHS input rejected: {reprStr error}")
  IO.println "source Core structural mapping places GREEN"

end Tests.SourceCoreDataPlaces
end
