import Solcore.SourceSemantics.CoreLowering.DataPlaceAssignmentSuccess
import Solcore.SourceSemantics.CoreLowering.Literals

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
