import Solcore.SourceSemantics.CoreLowering.DataPlaceLayoutCertificates
import Solcore.SourceSemantics.CoreLowering.BasicExpressionCertificates
import Solcore.SourceSemantics.CoreLowering.Literals

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
