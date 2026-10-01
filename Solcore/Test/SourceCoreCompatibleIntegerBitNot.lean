import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceBitNotLowerReflection
import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceBitNotFaults
import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceDescription
import Solcore.SourceSemantics.CoreLowering.CompatibleEncoding

#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! Retained Integer IR exercises the actual compatible compiler and independent
snapshot semantics. Source checker compound admission remains Word-only. -/
set_option autoImplicit false
set_option maxRecDepth 8192
namespace Tests.SourceCoreCompatibleIntegerBitNot
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceKeys
open SourceCoreCompatibleDataPlaces

private theorem except_get {α ε : Type} (result : Except ε α) (positive : result.toOption.isSome = true) :
    result = .ok (result.toOption.get positive) := by
  cases result with | error => simp [Except.toOption] at positive | ok => rfl
private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"compatible_lower_reflection", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def span : Syntax.SourceSpan := ⟨⟨.main, "compatible_lower_reflection.solc"⟩, 0, 1⟩
private def key : ExpressionId := ⟨⟨owner, 1⟩⟩
private def site : SourceCoreElaboration.ErrorSite := .occurrence ⟨owner, 0⟩
private def rootType : TypeSystem.Ty := .mapping .bool .integer
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private theorem catalogExists : (SourceCoreCompatibleCatalog.prepare signatures 100 [rootType]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 100 [rootType]).toOption.get catalogExists
private def compilation := SourceCoreCompatibleValues.Context.initial checked
private def binder : TypedBinder := ⟨⟨owner, 0⟩, "root", .mono rootType, [], false, none⟩
private def node : ExpressionNode := { id := key, span, type := .bool, form := .reference "true" (.builtinBoolean true) }
private def source : TypedSource := { owner, inputs := [binder], roots := [.expression key], nodes := [.expression node] }
private def assignment : AssignmentResolution := ⟨⟨binder.id, [.index key], .integer⟩, []⟩
private def context := (SourceSemantics.Context.ofSignatures signatures).withLocal binder.id binder.scheme
private def program : SourceSemantics.Program := ⟨signatures, [], []⟩
private def noFunctions (catalog : SourceCoreCompatibleCatalog.Catalog) : FunctionModel catalog where
  Represents := fun _ _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  source_function := False.elim
  extend := fun impossible _ _ _ => False.elim impossible
private theorem observations : FunctionObservations checked.catalog (noFunctions checked.catalog) (fun _ _ => False) := by
  intro _ _ _ _ _ _ _ impossible; exact impossible.elim
private theorem faithful : DataEquality.IdentityFaithful (fun _ _ => False) := by
  constructor <;> intros <;> contradiction
private theorem unique : NodeOccurrencesUnique source := by simp [NodeOccurrencesUnique, nodeOccurrenceIds, source]
private theorem contains : ContainsExpression source key node := lookupExpression?_sound (by cbv)
private def lowered : SourceCoreBasic.LoweredExpr := ⟨.bool, LanguageResult.success (.bool true)⟩
private def Child : GenericExpressionMeaning.Certificate := fun _ id code => id = key ∧ code = lowered

/-- The child reflection IH is proved uniformly, including every hidden-slot
renaming. Its source execution is constructed from the completed Core child. -/
private theorem childReflects (registry : SourceCoreRawMetadata.Registry) (faults : GenericExpressionMeaning.FaultRep) :
    GenericExpressionMeaning.Reflects (payloadModel checked registry (noFunctions checked.catalog))
      program context [] source Child faults := by
  intro scope id code certificate n found mapping world administrative environment canonical actual before store ξ value finalStore
    environments heaps locals agrees evaluated
  obtain ⟨rfl, rfl⟩ := certificate
  have nodeEq : n = node := Option.some.inj (found.symm.trans (show source.lookupExpression? key = some node by cbv))
  subst n
  cases evaluated with
  | inRight inner =>
    cases inner
    exact ⟨.value (.bool true), before, mapping, world, .value (.intro contains (.builtinBoolean rfl) .nil),
      .value (.bool true), heaps, .refl _, .refl _, .refl _ _, .refl _⟩

private theorem functionViews : FunctionRuntimeViews (noFunctions checked.catalog) := fun impossible => False.elim impossible
private theorem rootExists : (checked.catalog.project rootType).toOption.isSome = true := by cbv
private def rootCore := (checked.catalog.project rootType).toOption.get rootExists
private theorem rootProjected : checked.catalog.project rootType = .ok rootCore := except_get _ rootExists
private def scope : SourceCoreLocalCell.Scope := [(binder.id, rootCore)]
private def coreContext : Core.Context := [OptionalCell.referenceType rootCore]
private def before (initial : Option Dynamic.Value) : Dynamic.Heap := ⟨[⟨rootType, initial, none⟩]⟩
private def environment : Dynamic.Environment := [(binder.id, ⟨0⟩)]
private def world : StoreTyping := [OptionalCell.cellType rootCore]
private def nativeEnvironment : Environment := [.cellRef (OptionalCell.cellType rootCore) 0]
private theorem localAgrees (initial : Option Dynamic.Value) : Dynamic.EnvironmentAgrees (before initial) context.locals environment :=
  .cons (.intro .head) rfl (.ordinary rfl rfl) .nil
private theorem rootWritable : WritableLocal context binder.id rootType :=
  WritableLocal.withLocal_mono _ _ _ ⟨(TypeParameterBindersWellFormed.ofSignatures signatures).withLocal binder.id binder.scheme,
    .mapping (.builtin .bool) (.builtin .integer)⟩
private theorem keyTyped : ExpressionHasType source context key .bool := by
  apply ExpressionHasType.ofOrdinary (node := node) (rawType := .bool) contains
    (.reference (.builtinBoolean true)) (.bool ((TypeParameterBindersWellFormed.ofSignatures signatures).withLocal binder.id binder.scheme))
    (.bool ((TypeParameterBindersWellFormed.ofSignatures signatures).withLocal binder.id binder.scheme))
  · intro id member; cases member
  · exact .nil _
  · rfl

/-- The fixture admits its only retained child occurrence and calls the real
Basic compiler in that branch. It contains no evaluator or hypothetical code. -/
private def childCompiler : ExpressionLowerer := fun fuel source scope id reasonAt =>
  if id = key then SourceCoreBasic.lowerExpression fuel source scope id (reasonAt id)
  else .error (.missingExpression id)
private theorem childReceipt (id : ExpressionId) (code : SourceCoreBasic.LoweredExpr)
    (accepted : childCompiler 100 source scope id (fun _ => Word.zero) = .ok code) :
    ∃ node, source.lookupExpression? id = some node ∧ Child scope id code ∧
      HasType (SourceCoreLocalCell.coreContext scope ++ []) code.expression (LanguageResult.resultType code.type) checked.catalog.definitions := by
  unfold childCompiler at accepted
  split at accepted
  · rename_i same
    subst id
    have actual : SourceCoreBasic.lowerExpression 100 source scope key Word.zero = .ok lowered := by cbv
    rw [actual] at accepted
    cases accepted
    exact ⟨node, (by cbv), ⟨rfl, rfl⟩, .inRight .word .bool⟩
  · cases accepted

/-- A successful run of the real lowerer's output yields a complete source
assignment and final represented heap. Path, key views and both helper typing
receipts are extracted internally, not supplied by this fixture. -/
theorem actual_lower_reflects {code : Expr}
    (accepted : lower compilation checked.signatures childCompiler 100 source scope site assignment .equal none .bool
      lowered.expression (fun _ => Word.zero) Word.zero Word.zero (fun _ => Word.zero) = .ok code)
    (typed : HasType coreContext code (LanguageResult.resultType .bool) checked.catalog.definitions)
    {registry : SourceCoreRawMetadata.Registry} (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {initial : Option Dynamic.Value} {native : Value}
    (initialRep : GenericHeap.CellRepresents (payloadModel checked registry (noFunctions checked.catalog)) [] []
      ⟨rootType, initial, none⟩ native rootCore)
    {after : Store}
    (completed : Evaluates nativeEnvironment [native] code (.inRight .word (.bool true)) after) :
    ∃ updated sourceAfter finalMap finalWorld,
      Dynamic.SourcePlaceSnapshotUpdate program context [] source Dynamic.BitNotSnapshot
        environment (before initial) assignment.target updated sourceAfter ∧
      HeapRepresents checked registry (noFunctions checked.catalog) finalMap finalWorld sourceAfter after ∧
      LocationMap.Extends [0] finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved [0] [native] finalMap after ∧ Dynamic.HeapMetadataExtend (before initial) sourceAfter := by
  have empty : HeapRepresents checked registry (noFunctions checked.catalog) [] [] ⟨[]⟩ [] := GenericHeap.HeapRepresents.empty
  obtain ⟨heaps, reference⟩ := empty.allocate initialRep Dynamic.Heap.Allocates.append
  have environments : DataHeap.EnvRepresents (storageCatalog checked.catalog) [0] world [] scope environment nativeEnvironment :=
    .cons reference (.nil .nil)
  have binding : ∀ actual, rootBinder source assignment.target.root = .ok actual → actual = binder := by
    intro actual found
    exact Except.ok.inj (found.symm.trans (show rootBinder source assignment.target.root = .ok binder by cbv))
  have reflected := CompatiblePlaceBitNotLowerReflection.reflects_numeric (compilation := compilation)
    (ambient := .original checked.catalog.definitions) (functions := noFunctions checked.catalog) (certificate := Child)
    unique rfl (fun actual found => by cases binding actual found; exact .index keyTyped (.nil _))
    (fun actual found => by cases binding actual found; exact rootWritable) (by simp [assignment])
    (fun id code accepted => let ⟨node, found, child, _⟩ := childReceipt id code accepted; ⟨node, found, child⟩) accepted typed
    registryExtension (childReflects registry (fun _ _ => True)) functionViews faithful observations
    (fun _ _ => True.intro) (fun _ => True.intro) (.inr rfl) environments heaps (localAgrees initial) completed
  cases reflected with
  | fault _ resultEq => cases resultEq
  | committed trace heaps maps worlds frame metadata length continuation =>
    simp only [shift, List.range, List.range.loop, List.foldl, Expr.weakenAt, lowered, LanguageResult.success] at continuation
    cases continuation with
    | inRight valueEvaluated =>
      cases valueEvaluated
      exact ⟨_, _, _, _, trace, heaps, maps, worlds, frame, metadata⟩

/-- Direct consumer of the real checked wrapper: its private compiler work
is recovered from success and its public typing field. -/
theorem checked_lower_reflects {certified : Certified checked.catalog.definitions coreContext .bool}
    (accepted : lowerChecked compilation checked.signatures childCompiler 100 source scope site assignment .equal none .bool
      lowered.expression (fun _ => Word.zero) Word.zero Word.zero (fun _ => Word.zero) checked.catalog.definitions coreContext = .ok certified)
    {registry : SourceCoreRawMetadata.Registry} (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {initial : Option Dynamic.Value} {native : Value}
    (initialRep : GenericHeap.CellRepresents (payloadModel checked registry (noFunctions checked.catalog)) [] []
      ⟨rootType, initial, none⟩ native rootCore)
    {after : Store}
    (completed : Evaluates nativeEnvironment [native] certified.expression (.inRight .word (.bool true)) after) :
    ∃ updated sourceAfter finalMap finalWorld,
      Dynamic.SourcePlaceSnapshotUpdate program context [] source Dynamic.BitNotSnapshot
        environment (before initial) assignment.target updated sourceAfter ∧
      HeapRepresents checked registry (noFunctions checked.catalog) finalMap finalWorld sourceAfter after ∧
      LocationMap.Extends [0] finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved [0] [native] finalMap after ∧ Dynamic.HeapMetadataExtend (before initial) sourceAfter :=
  actual_lower_reflects (CompatiblePlaceCompilerCertificates.lower_of_lowerChecked accepted) certified.typed registryExtension initialRep completed

private def exercise {certified : Certified checked.catalog.definitions coreContext .bool}
    (accepted : lowerChecked compilation checked.signatures childCompiler 100 source scope site assignment .equal none .bool
      lowered.expression (fun _ => Word.zero) Word.zero Word.zero (fun _ => Word.zero) checked.catalog.definitions coreContext = .ok certified)
    {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {initial : Option Dynamic.Value} {native : Value}
    (initialRep : GenericHeap.CellRepresents (payloadModel checked registry (noFunctions checked.catalog)) [] []
      ⟨rootType, initial, none⟩ native rootCore)
    (expected : SourceCoreDataValues.Value) : IO Unit := do
  let start := Core.State.initial certified.expression nativeEnvironment [native]
  match ran : runStateful 200000 start with
  | .done result after =>
    if success : result = .inRight .word (.bool true) then
      have _source := checked_lower_reflects accepted extension initialRep (success ▸ runStateful_evaluation_sound ran)
      unless after.length == 1 + 3 * (checked.catalog.entries.length + 1) do
        throw (IO.userError "compatible Integer bit-not admin count changed")
      match after.read? 0 with
      | some (.inRight .unit value) =>
        let outputContext : SourceCoreCompatibleValues.Context := ⟨checked, registry, extension⟩
        match SourceCoreCompatibleValues.decode 100 outputContext rootType value with
        | .ok actual => unless actual == expected do
            throw (IO.userError "compatible Integer bit-not raw metadata or ordered duplicates changed")
        | .error error => throw (IO.userError s!"compatible Integer bit-not decode failed {reprStr error}")
      | _ => throw (IO.userError "compatible Integer bit-not missing mapped write")
      match runStateful 17 start with
      | .outOfFuel checkpoint => unless runStateful 200000 checkpoint == .done result after do
          throw (IO.userError "compatible Integer bit-not resume changed result")
      | _ => throw (IO.userError "compatible Integer bit-not expected checkpoint")
    else throw (IO.userError "compatible Integer bit-not expected success")
  | other => throw (IO.userError s!"compatible Integer bit-not run failed {reprStr other}")

private def seven : Int := 7
private def nine : Int := 9
private def carrier : SourceCoreDataValues.Value :=
  .mapping (.comptime .bool) (.comptime .integer) [(.bool true, .integer seven), (.bool true, .integer nine)]
private def sourceValue : Dynamic.Value :=
  .mapping (.comptime .bool) (.comptime .integer) [(.bool true, .integer seven), (.bool true, .integer nine)]
private theorem carrierMeaning : CompatibleEncoding.Means carrier sourceValue :=
  .mapping (.prepend (.bool true) (.integer seven) (.prepend (.bool true) (.integer nine) .empty))

def run : IO Unit := do
  match accepted : lowerChecked compilation checked.signatures childCompiler 100 source scope site assignment .equal none .bool
      lowered.expression (fun _ => Word.zero) Word.zero Word.zero (fun _ => Word.zero) checked.catalog.definitions coreContext with
  | .error error => throw (IO.userError s!"compatible Integer bit-not rejected {reprStr error}")
  | .ok _certified =>
      exercise accepted (.refl _) (.uninitialized rootProjected)
        (.mapping .bool .integer [(.bool true, .integer (-1))])
      match encoded : SourceCoreCompatibleValues.encode 100 compilation rootType carrier with
      | .error error => throw (IO.userError s!"compatible Integer bit-not encode failed {reprStr error}")
      | .ok encodedValue =>
        have represented := CompatibleEncoding.encode_represents_at (functions := noFunctions checked.catalog) encoded carrierMeaning [] []
        have same := Except.ok.inj (represented.projection.symm.trans rootProjected)
        exercise accepted encodedValue.preserves (.initialized (same ▸ represented))
          (.mapping (.comptime .bool) (.comptime .integer) [(.bool true, .integer (~~~seven)), (.bool true, .integer nine)])
  IO.println "retained Integer absent-RHS bit-not actual compiler/source meaning/Unit slot/raw duplicate order/virtual root/resume GREEN"

end Tests.SourceCoreCompatibleIntegerBitNot
