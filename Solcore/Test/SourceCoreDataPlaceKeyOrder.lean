import Solcore.SourceSemantics.CoreLowering.DataPlaceKeyOrder
import Solcore.SourceSemantics.CoreLowering.BasicExpressionCertificates
import Solcore.SourceSemantics.CoreLowering.Literals

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
