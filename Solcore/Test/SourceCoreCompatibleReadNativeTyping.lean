import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReadNativeTyping

/-! Native typing is obtained from actual compatible read acceptance and
independent source typing. The fixtures include staged mapping metadata and
arbitrary administrative context extensions. Unused invalid sum annotations
demonstrate why raw runtime typing cannot replace checked projection. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 65536
namespace Tests.SourceCoreCompatibleReadNativeTyping
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CompatibleExpressionReads

/-- An external consumer needs neither a native child typing assumption nor
a source or Core execution premise. -/
theorem actual_read_native {fuel : Nat} {values : ValuesContext} {source : TypedSource}
    {sourceContext : SourceSemantics.Context} {reasonAt : ExpressionId → Word}
    {scope : Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (accepted : SourceCoreCompatibleDataExpressions.lowerRead fuel values source scope id (reasonAt id) = .ok lowered.expression)
    (read : SourceCoreCompatibleDataExpressions.readExpression values.checked source id = .ok (node, lowered.type))
    (unique : NodeOccurrencesUnique source) (declarations : ScopeDeclarations source scope sourceContext)
    (typed : ExpressionHasType source sourceContext id node.type) (administrative : Core.Context) :
    HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
      (LanguageResult.resultType lowered.type) values.checked.catalog.definitions :=
  loweredRead_native_hasType accepted read unique declarations typed administrative

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"read_native", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "read_native.solc"⟩, 0, 1⟩
private def id : ExpressionId := ⟨⟨owner, 1⟩⟩
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def binder (type : TypeSystem.Ty) : TypedBinder := ⟨⟨owner, 0⟩, "value", .mono type, [], false, none⟩
private def node (type : TypeSystem.Ty) : ExpressionNode :=
  { id, span, type, form := .reference "value" (.local (binder type).id) }
private def source (type : TypeSystem.Ty) : TypedSource :=
  { owner, inputs := [binder type], roots := [.expression id], nodes := [.expression (node type)] }
private def sourceContext (type : TypeSystem.Ty) :=
  (SourceSemantics.Context.ofSignatures signatures).withLocal (binder type).id (binder type).scheme
private def reason : Word := Word.ofNatModulo 17
private def scope (type : Ty) : SourceCoreLocalCell.Scope := [((binder .bool).id, type)]
private theorem unique (type : TypeSystem.Ty) : NodeOccurrencesUnique (source type) := by
  simp [NodeOccurrencesUnique, nodeOccurrenceIds, source]

private theorem declarations (sourceType : TypeSystem.Ty) (type : Ty) :
    ScopeDeclarations (source sourceType) (scope type) (sourceContext sourceType) := by
  intro id declared index native selected accepted
  simp only [scope, SourceCoreLocalCell.lookup?] at selected
  split at selected
  · rename_i same
    subst id
    have actual : SourceCoreDataPlaces.rootBinder (source sourceType) (binder .bool).id = .ok (binder sourceType) := by
      simp [SourceCoreDataPlaces.rootBinder, SourceCoreDataPlaces.declaredBinders, source, binder, node, TypeSystem.Scheme.mono]
    rw [actual] at accepted
    cases accepted
    exact .head
  · simp at selected

private theorem sourceTyped {type : TypeSystem.Ty} (typed : TypeAdmissible (sourceContext type) type) :
    ExpressionHasType (source type) (sourceContext type) id type := by
  have contains : ContainsExpression (source type) id (node type) := lookupExpression?_sound (by rfl)
  have scheme : SchemeWellFormed (sourceContext type) (binder type).scheme := SchemeWellFormed.monoAdmissible typed
  apply ExpressionHasType.ofOrdinary (node := node type) (rawType := type) contains
    (.reference (.local (.head) (.head) (.intro (.empty _ _ rfl) scheme []
      .empty (by intro metavariable replacement member; cases member) (by exact SchemeInstantiates.empty_apply type)
      (by simp) (by intro _ member; cases member) (.nil)))) typed typed
  · intro requirement member; cases member
  · exact .nil _
  · rfl

private def mappingType : TypeSystem.Ty := .mapping (.comptime .bool) .word
private theorem prepared : (SourceCoreCompatibleCatalog.prepare signatures 10 [.bool, mappingType]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 10 [.bool, mappingType]).toOption.get prepared
private def values := SourceCoreCompatibleValues.Context.initial checked
private def boolLowered : SourceCoreBasic.LoweredExpr := ⟨.bool, OptionalCell.read .bool (.var 0) reason⟩

theorem ordinary_checked_read (administrative : Core.Context) :
    HasType (SourceCoreLocalCell.coreContext (scope .bool) ++ administrative) boolLowered.expression
      (LanguageResult.resultType .bool) checked.catalog.definitions := by
  apply actual_read_native (source := source .bool) (sourceContext := sourceContext .bool)
    (reasonAt := fun _ => reason) (node := node .bool)
    (show SourceCoreCompatibleDataExpressions.lowerRead 100 values (source .bool) (scope .bool) id reason = .ok boolLowered.expression by rfl)
    (show SourceCoreCompatibleDataExpressions.readExpression checked (source .bool) id = .ok (node .bool, .bool) by rfl)
    (unique _) (declarations _ _)
  exact sourceTyped (.bool ((TypeParameterBindersWellFormed.ofSignatures signatures).withLocal (binder .bool).id (binder .bool).scheme))

private theorem mappingProjected : (checked.catalog.project mappingType).toOption.isSome = true := by rfl
private def mappingNative := (checked.catalog.project mappingType).toOption.get mappingProjected
private def mappingAction := SourceCoreCompatibleDataExpressions.lowerRead 5 values (source mappingType) (scope mappingNative) id reason

theorem mapping_checked_read {code : Expr} (accepted : mappingAction = .ok code) (administrative : Core.Context) :
    HasType (SourceCoreLocalCell.coreContext (scope mappingNative) ++ administrative) code
      (LanguageResult.resultType mappingNative) checked.catalog.definitions := by
  apply actual_read_native (source := source mappingType) (sourceContext := sourceContext mappingType)
    (reasonAt := fun _ => reason) (lowered := ⟨mappingNative, code⟩) (node := node mappingType)
    accepted
    (show SourceCoreCompatibleDataExpressions.readExpression checked (source mappingType) id = .ok (node mappingType, mappingNative) by rfl)
    (unique _) (declarations _ _)
  exact sourceTyped (.mapping
    (.comptime (.bool ((TypeParameterBindersWellFormed.ofSignatures signatures).withLocal (binder mappingType).id (binder mappingType).scheme)))
    (.word ((TypeParameterBindersWellFormed.ofSignatures signatures).withLocal (binder mappingType).id (binder mappingType).scheme)))

private def missingData : Ty := .namedData ⟨0⟩
theorem unused_annotation_runtime_typed :
    RuntimeValueHasType [] (.inLeft missingData .unit) (.sum .unit missingData) [] := .inLeft .unit
theorem unused_annotation_quoted :
    SourceCoreCompatibleDataExpressions.quote (.inLeft missingData .unit) = some (.inLeft missingData .unit) := rfl
theorem unused_annotation_rejected (context : Core.Context) :
    ¬ HasType context (.inLeft missingData .unit) (.sum .unit missingData) [] := by
  intro typed
  cases typed with
  | inLeft wellFormed _ => cases wellFormed with | namedData found => cases found

def run : IO Unit := do
  let code ← match accepted : mappingAction with
    | .error error => throw (IO.userError s!"actual staged mapping read: {reprStr error}")
    | .ok code =>
      have derived : HasType (SourceCoreLocalCell.coreContext (scope mappingNative)) code
          (LanguageResult.resultType mappingNative) checked.catalog.definitions := by
        simpa only [List.append_nil] using mapping_checked_read accepted []
      let _derived := derived
      pure code
  let encoded ← match SourceCoreCompatibleValues.encode 5 values mappingType (.mapping (.comptime .bool) .word []) with
    | .error error => throw (IO.userError s!"staged empty mapping: {reprStr error}")
    | .ok encoded => pure encoded.value
  let initial : Store := [.integer 77, .inLeft mappingNative .unit]
  let expected : Value := .inRight .word encoded
  unless Core.infer? (SourceCoreLocalCell.coreContext (scope mappingNative)) code checked.catalog.definitions =
      some (LanguageResult.resultType mappingNative) do
    throw (IO.userError "actual mapping read native typing changed")
  for fuel in [0, 1, 3, 97, 2000] do
    let state := State.initial code [.cellRef (OptionalCell.cellType mappingNative) 1] initial
    let completed := match Core.runStateful fuel state with
      | .outOfFuel suspended => Core.runStateful 2000 suspended
      | other => other
    match completed with
    | .done actual store =>
      unless actual == expected && store == [.integer 77, .inRight .unit encoded] do
        throw (IO.userError "staged lazy mapping read lost metadata, prefix, write or resumed result")
    | other => throw (IO.userError s!"actual mapping read completion: {reprStr other}")
  IO.println "compatible native read typing: accepted ordinary/staged mapping reads, checked unused annotations, retained metadata/prefix and real resume GREEN"

end Tests.SourceCoreCompatibleReadNativeTyping
