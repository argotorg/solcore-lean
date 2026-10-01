import Solcore.SourceSemantics.CoreLowering.CompatibleBareBitNotLowering

#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxRecDepth 8192
namespace Tests.SourceCoreCompatibleBareBitNot
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap SourceCoreCompatibleDataPlaces

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"bare_bitnot", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def site : SourceCoreElaboration.ErrorSite := .occurrence ⟨owner, 0⟩
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private theorem catalogExists : (SourceCoreCompatibleCatalog.prepare signatures 100 [.word, .integer]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 100 [.word, .integer]).toOption.get catalogExists
private def compilation := SourceCoreCompatibleValues.Context.initial checked
private def binder (type : TypeSystem.Ty) : TypedBinder := ⟨⟨owner, 0⟩, "root", .mono type, [], false, none⟩
private def source (type : TypeSystem.Ty) : TypedSource := { owner, inputs := [binder type], roots := [], nodes := [] }
private def assignment (type : TypeSystem.Ty) : AssignmentResolution := ⟨⟨(binder type).id, [], type⟩, []⟩
private def scope (type : Core.Ty) : SourceCoreLocalCell.Scope := [((binder .word).id, type)]
private def nativeEnvironment (type : Core.Ty) : Environment := [.cellRef (OptionalCell.cellType type) 0]
private def nativeContext (type : Core.Ty) : Core.Context := [OptionalCell.referenceType type]
private def wordContext := (SourceSemantics.Context.ofSignatures signatures).withLocal (binder .word).id (binder .word).scheme
private def program : SourceSemantics.Program := ⟨signatures, [], []⟩
private def sourceEnvironment : Dynamic.Environment := [((binder .word).id, ⟨0⟩)]
private def sourceHeap (initial : Option Dynamic.Value) : Dynamic.Heap := ⟨[⟨.word, initial, none⟩]⟩
private def world : StoreTyping := [OptionalCell.cellType .word]
private def noFunctions (catalog : SourceCoreCompatibleCatalog.Catalog) : FunctionModel catalog where
  Represents := fun _ _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  source_function := False.elim
  extend := fun impossible _ _ _ => False.elim impossible
private theorem observations : FunctionObservations checked.catalog (noFunctions checked.catalog) (fun _ _ => False) := by
  intro _ _ _ _ _ _ _ impossible; exact impossible.elim
private theorem localAgrees (initial : Option Dynamic.Value) :
    Dynamic.EnvironmentAgrees (sourceHeap initial) wordContext.locals sourceEnvironment :=
  .cons (.intro .head) rfl (.ordinary rfl rfl) .nil
private theorem rootWritable : WritableLocal wordContext (binder .word).id .word :=
  WritableLocal.withLocal_mono _ _ _ ⟨(TypeParameterBindersWellFormed.ofSignatures signatures).withLocal (binder .word).id (binder .word).scheme,
    .builtin .word⟩
private theorem writable : ∀ actual, rootBinder (source .word) (assignment .word).target.root = .ok actual →
    WritableLocal wordContext (assignment .word).target.root actual.scheme.body := by
  intro actual found
  have same := Except.ok.inj (found.symm.trans
    (show rootBinder (source .word) (assignment .word).target.root = .ok (binder .word) by cbv))
  subst actual
  exact rootWritable

/-- A child compiler which always rejects proves no source child is lowered
by this branch. It is not used as a replacement expression compiler. -/
private def noChildren : ExpressionLowerer := fun _ _ _ id _ => .error (.missingExpression id)
private def invalid : Word := Word.ofNatModulo 41
private def projectionFault : Word := Word.ofNatModulo 73
private def next : Expr := LanguageResult.success (.bool true)
private def compile (raw : TypeSystem.Ty) (type : Core.Ty) (tail : Expr := next) :=
  lowerChecked compilation checked.signatures noChildren 100 (source raw) (scope type) site (assignment raw) .equal none .bool tail
    (fun _ => Word.zero) projectionFault invalid (fun _ => Word.zero) checked.catalog.definitions (nativeContext type)

/-- Actual compiler receipt plus actual completed native execution imply an
independent source result, with no prior source execution or child IH. -/
theorem actual_reflects {certified : Certified checked.catalog.definitions (nativeContext .word) .bool}
    (accepted : compile .word .word = .ok certified)
    {initial : Option Dynamic.Value} {native : Value}
    (initialRep : GenericHeap.CellRepresents (payloadModel checked compilation.registry (noFunctions checked.catalog)) [] []
      ⟨.word, initial, none⟩ native .word)
    {result : Value} {after : Store}
    (completed : Evaluates (nativeEnvironment .word) [native] certified.expression result after) :
    CompatiblePlaceBitNotMeaning.Result checked compilation.registry (noFunctions checked.catalog) program wordContext [] (source .word)
      (fun _ _ => True) (assignment .word).target sourceEnvironment (nativeEnvironment .word)
      (sourceHeap initial) [native] [0] world next .bool result after := by
  have empty : HeapRepresents checked compilation.registry (noFunctions checked.catalog) [] [] ⟨[]⟩ [] := GenericHeap.HeapRepresents.empty
  obtain ⟨heaps, reference⟩ := empty.allocate initialRep Dynamic.Heap.Allocates.append
  have environments : DataHeap.EnvRepresents (storageCatalog checked.catalog) [0] world [] (scope .word) sourceEnvironment (nativeEnvironment .word) :=
    .cons reference (.nil .nil)
  exact CompatibleBareBitNotLowering.reflects writable rfl (.inl rfl) observations environments heaps (localAgrees initial)
    (CompatiblePlaceCompilerCertificates.lower_of_lowerChecked accepted) True.intro completed

private theorem absentFault : Dynamic.SourcePlaceBitNotFaults program wordContext [] (source .word) sourceEnvironment
    (sourceHeap none) (assignment .word).target (.invalidUnaryOperand .bitNot) (sourceHeap none) :=
  .uninitialized (CompatibleBareBitNotMeaning.resolves rfl .head (.intro .head)
    (.uninitialized (by rintro ⟨a, b, impossible⟩; cases impossible))) rfl

/-- The source absent-operand rule produces the actual compiler's exact token
and preserves the store. This instantiates the independent fault direction. -/
theorem actual_absent {certified : Certified checked.catalog.definitions (nativeContext .word) .bool}
    (accepted : compile .word .word = .ok certified) :
    Evaluates (nativeEnvironment .word) [.inLeft .word .unit] certified.expression (.inLeft .bool (.word invalid)) [.inLeft .word .unit] := by
  have empty : HeapRepresents checked compilation.registry (noFunctions checked.catalog) [] [] ⟨[]⟩ [] := GenericHeap.HeapRepresents.empty
  obtain ⟨heaps, reference⟩ := empty.allocate (GenericHeap.CellRepresents.uninitialized (show checked.catalog.project .word = .ok .word by rfl))
    Dynamic.Heap.Allocates.append
  have environments : DataHeap.EnvRepresents (storageCatalog checked.catalog) [0] world [] (scope .word) sourceEnvironment (nativeEnvironment .word) :=
    .cons reference (.nil .nil)
  exact (CompatibleBareBitNotLowering.preserves_fault writable rfl (.inl rfl) observations environments heaps (localAgrees none)
    (CompatiblePlaceCompilerCertificates.lower_of_lowerChecked accepted) absentFault).2.2

private def seven : Word := Word.ofNatModulo 7
private theorem sourceUpdate : Dynamic.SourcePlaceSnapshotUpdate program wordContext [] (source .word) Dynamic.BitNotSnapshot
    sourceEnvironment (sourceHeap (some (.word seven))) (assignment .word).target (.word seven.bitNot)
    (sourceHeap (some (.word seven.bitNot))) :=
  .intro (CompatibleBareBitNotMeaning.resolves rfl .head (.intro .head) .initialized)
    (.intro (.intro .head) rfl .initialized (.leaf (.word seven)) (DataPlaceCommitReflection.source_writes (.intro .head) _))

/-- The success direction consumes an independent snapshot update, with one
physical write and the original map/world. -/
theorem actual_preserves {code : Expr}
    (accepted : lower compilation checked.signatures noChildren 100 (source .word) (scope .word) site (assignment .word) .equal none
      .unit (LanguageResult.success .unit) (fun _ => Word.zero) projectionFault invalid (fun _ => Word.zero) = .ok code) :
    ∃ after, Evaluates (nativeEnvironment .word) [.inRight .unit (.word seven)] code (.inRight .word .unit) after ∧
      HeapRepresents checked compilation.registry (noFunctions checked.catalog) [0] world
        (sourceHeap (some (.word seven.bitNot))) after ∧
      AdministrativePreserved [0] [.inRight .unit (.word seven)] [0] after ∧
      Dynamic.HeapMetadataExtend (sourceHeap (some (.word seven))) (sourceHeap (some (.word seven.bitNot))) := by
  have empty : HeapRepresents checked compilation.registry (noFunctions checked.catalog) [] [] ⟨[]⟩ [] := GenericHeap.HeapRepresents.empty
  obtain ⟨heaps, reference⟩ := empty.allocate (GenericHeap.CellRepresents.initialized (ValueRep.word seven)) Dynamic.Heap.Allocates.append
  have environments : DataHeap.EnvRepresents (storageCatalog checked.catalog) [0] world [] (scope .word) sourceEnvironment (nativeEnvironment .word) :=
    .cons reference (.nil .nil)
  exact CompatibleBareBitNotLowering.preserves writable rfl (.inl rfl) observations environments heaps
    (localAgrees (some (.word seven))) accepted sourceUpdate

private def exercise (raw : TypeSystem.Ty) (type : Core.Ty) (initial expected : Value) (succeeds : Bool) : IO Unit := do
  match compile raw type with
  | .error error => throw (IO.userError s!"bare bit-not compile: {reprStr error}")
  | .ok certified =>
    let start := State.initial certified.expression (nativeEnvironment type) [initial]
    let wanted := if succeeds then Value.inRight .word (.bool true) else .inLeft .bool (.word invalid)
    let after := [expected]
    unless runStateful 1000 start == .done wanted after do throw (IO.userError "bare bit-not output/store mismatch")
    match runStateful 7 start with
    | .outOfFuel checkpoint => unless runStateful 1000 checkpoint == .done wanted after do
        throw (IO.userError "bare bit-not resume mismatch")
    | _ => throw (IO.userError "bare bit-not checkpoint missing")
  -- A continuation which writes the root must also be skipped on absence.
  let effect := Expr.letE (.storeCell (.var 0) (.inLeft type .unit)) (LanguageResult.success (.bool true))
  match compile raw type effect with
  | .error error => throw (IO.userError s!"bare bit-not effect compile: {reprStr error}")
  | .ok certified =>
    let empty := Value.inLeft type .unit
    unless runStateful 1000 (State.initial certified.expression (nativeEnvironment type) [empty]) ==
        .done (.inLeft .bool (.word invalid)) [empty] do throw (IO.userError "absent operand ran continuation")

def run : IO Unit := do
  match accepted : compile .word .word with
  | .error error => throw (IO.userError s!"bare bit-not Word compile: {reprStr error}")
  | .ok certified =>
    have _finite := actual_absent accepted
    match ran : runStateful 1000 (State.initial certified.expression (nativeEnvironment .word) [.inRight .unit (.word seven)]) with
    | .done result after =>
      have _source := actual_reflects accepted (.initialized (.word seven)) (runStateful_evaluation_sound ran)
      unless result == .inRight .word (.bool true) && after == [.inRight .unit (.word seven.bitNot)] do
        throw (IO.userError "bare bit-not proof consumer mismatch")
    | _ => throw (IO.userError "bare bit-not proof consumer incomplete")
  exercise .word .word (.inLeft .word .unit) (.inLeft .word .unit) false
  exercise .word .word (.inRight .unit (.word seven)) (.inRight .unit (.word seven.bitNot)) true
  -- Integer compound remains a trusted retained-IR profile, not checker admission.
  exercise .integer .integer (.inLeft .integer .unit) (.inLeft .integer .unit) false
  for value in [0, 7, -7, -(2^300 : Int)] do
    exercise .integer .integer (.inRight .unit (.integer value)) (.inRight .unit (.integer (~~~value))) true
  IO.println "bare bit-not actual lowering/independent meaning/absent store preservation/no children/single write/resume GREEN"

end Tests.SourceCoreCompatibleBareBitNot
