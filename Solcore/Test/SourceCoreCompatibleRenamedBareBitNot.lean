import Solcore.SourceSemantics.CoreLowering.CompatibleRenamedBareBitNotLowering

#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
set_option maxRecDepth 8192
namespace Tests.SourceCoreCompatibleRenamedBareBitNot
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap SourceCoreCompatibleDataPlaces

private def moduleId : Workspace.ModuleId := ⟨.main, ⟨[⟨"renamed_bare_bitnot", by decide⟩], by decide⟩⟩
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
private def reference (type : Core.Ty) : Value := .cellRef (OptionalCell.cellType type) 0

-- This existing closure is captured before insertion. Its body reads the same
-- physical root after the unary write, without changing its captured environment.
private def reader (type : Core.Ty) : Value :=
  .closure .unit type (.caseE (.loadCell (.var 1)) (if type = .integer then .integer 0 else .word Word.zero) (.var 0)) [reference type]
private def canonical (type : Core.Ty) : Environment := [reference type, reader type]
private def actual (type : Core.Ty) : Environment := [.bool false, .unit, reference type, reader type]
private def nativeContext (type : Core.Ty) : Core.Context := [OptionalCell.referenceType type, .function .unit type]
private def actualContext (type : Core.Ty) : Core.Context := [.bool, .unit, OptionalCell.referenceType type, .function .unit type]
private def embedding : Renaming := fun index => index + 2
private theorem agrees (type : Core.Ty) : ReadOnly.EnvironmentsAgree embedding (canonical type) (actual type) := by
  intro index value found
  change (.bool false :: .unit :: canonical type)[index + 2]? = some value
  simpa using found

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
private theorem writable : ∀ found, rootBinder (source .word) (assignment .word).target.root = .ok found →
    WritableLocal wordContext (assignment .word).target.root found.scheme.body := by
  intro found selected
  have same := Except.ok.inj (selected.symm.trans
    (show rootBinder (source .word) (assignment .word).target.root = .ok (binder .word) by cbv))
  subst found
  exact rootWritable
private theorem readerTyped : RuntimeValueHasType world (reader .word) (.function .unit .word) checked.catalog.definitions :=
  .closure (.cons (.cellRef rfl) .nil) (.caseE (.loadCell (.var rfl)) .word (.var rfl))
private theorem actualTyped : RuntimeEnvironmentHasTypes world (actual .word) (actualContext .word) checked.catalog.definitions :=
  .cons .bool (.cons .unit (.cons (.cellRef rfl) (.cons readerTyped .nil)))

private def noChildren : ExpressionLowerer := fun _ _ _ id _ => .error (.missingExpression id)
private def invalid : Word := Word.ofNatModulo 41
private def projectionFault : Word := Word.ofNatModulo 73
private def next : Expr := LanguageResult.success (.apply (.var 1) .unit)
private def compile (raw : TypeSystem.Ty) (type : Core.Ty) (tail : Expr := next) :=
  lowerChecked compilation checked.signatures noChildren 100 (source raw) (scope type) site (assignment raw) .equal none type tail
    (fun _ => Word.zero) projectionFault invalid (fun _ => Word.zero) checked.catalog.definitions (nativeContext type)

/-- Actual compiler completion reconstructs an independent source fault or
write and seven typed continuation slots in a genuinely inserted environment. -/
theorem actual_reflects {certified : Certified checked.catalog.definitions (nativeContext .word) .word}
    (accepted : compile .word .word = .ok certified)
    {initial : Option Dynamic.Value} {native : Value}
    (initialRep : GenericHeap.CellRepresents (payloadModel checked compilation.registry (noFunctions checked.catalog)) [] []
      ⟨.word, initial, none⟩ native .word)
    {result : Value} {after : Store}
    (completed : Evaluates (actual .word) [native] (certified.expression.rename embedding) result after) :
    ∃ prepared, CompatibleRenamedBareBitNot.Result checked compilation.registry (noFunctions checked.catalog) program wordContext [] (source .word)
      (fun _ _ => True) prepared (assignment .word).target sourceEnvironment (sourceHeap initial) [native] [0] world
      (actual .word) (actualContext .word) embedding next .word result after := by
  have empty : HeapRepresents checked compilation.registry (noFunctions checked.catalog) [] [] ⟨[]⟩ [] := GenericHeap.HeapRepresents.empty
  obtain ⟨heaps, ref⟩ := empty.allocate initialRep Dynamic.Heap.Allocates.append
  have environments : DataHeap.EnvRepresents (storageCatalog checked.catalog) [0] world [.function .unit .word]
      (scope .word) sourceEnvironment (canonical .word) := .cons ref (.nil (.cons readerTyped .nil))
  exact CompatibleRenamedBareBitNot.reflects_of_lower writable rfl (.inl rfl) observations environments heaps (localAgrees initial)
    (agrees .word) actualTyped (CompatiblePlaceCompilerCertificates.lower_of_lowerChecked accepted) True.intro completed

private theorem absentFault : Dynamic.SourcePlaceBitNotFaults program wordContext [] (source .word) sourceEnvironment
    (sourceHeap none) (assignment .word).target (.invalidUnaryOperand .bitNot) (sourceHeap none) :=
  .uninitialized (CompatibleBareBitNotMeaning.resolves rfl .head (.intro .head)
    (.uninitialized (by rintro ⟨a, b, impossible⟩; cases impossible))) rfl

theorem actual_absent {certified : Certified checked.catalog.definitions (nativeContext .word) .word}
    (accepted : compile .word .word = .ok certified) :
    Evaluates (actual .word) [.inLeft .word .unit] (certified.expression.rename embedding)
      (.inLeft .word (.word invalid)) [.inLeft .word .unit] := by
  have empty : HeapRepresents checked compilation.registry (noFunctions checked.catalog) [] [] ⟨[]⟩ [] := GenericHeap.HeapRepresents.empty
  obtain ⟨heaps, ref⟩ := empty.allocate (GenericHeap.CellRepresents.uninitialized (show checked.catalog.project .word = .ok .word by rfl))
    Dynamic.Heap.Allocates.append
  have environments : DataHeap.EnvRepresents (storageCatalog checked.catalog) [0] world [.function .unit .word]
      (scope .word) sourceEnvironment (canonical .word) := .cons ref (.nil (.cons readerTyped .nil))
  exact (CompatibleRenamedBareBitNot.preserves_fault_of_lower writable rfl (.inl rfl) observations environments heaps
    (localAgrees none) (agrees .word) (CompatiblePlaceCompilerCertificates.lower_of_lowerChecked accepted) absentFault).2.2

private def seven : Word := Word.ofNatModulo 7
private theorem sourceUpdate : Dynamic.SourcePlaceSnapshotUpdate program wordContext [] (source .word) Dynamic.BitNotSnapshot
    sourceEnvironment (sourceHeap (some (.word seven))) (assignment .word).target (.word seven.bitNot)
    (sourceHeap (some (.word seven.bitNot))) :=
  .intro (CompatibleBareBitNotMeaning.resolves rfl .head (.intro .head) .initialized)
    (.intro (.intro .head) rfl .initialized (.leaf (.word seven)) (DataPlaceCommitReflection.source_writes (.intro .head) _))

/-- The independent source update supplies the exact native prefix and a
typed actual continuation. No source or Core continuation run is a premise. -/
theorem actual_preserves_prefix {certified : Certified checked.catalog.definitions (nativeContext .word) .word}
    (accepted : compile .word .word = .ok certified) :
    ∃ prepared replacement finalStore slots,
      ValueRep checked compilation.registry (noFunctions checked.catalog) [0] world prepared.route.rootSourceType (.word seven.bitNot) replacement prepared.route.rootType ∧
      HeapRepresents checked compilation.registry (noFunctions checked.catalog) [0] world (sourceHeap (some (.word seven.bitNot))) finalStore ∧
      AdministrativePreserved [0] [.inRight .unit (.word seven)] [0] finalStore ∧
      Dynamic.HeapMetadataExtend (sourceHeap (some (.word seven))) (sourceHeap (some (.word seven.bitNot))) ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes world (slots ++ actual .word) (CompatibleRenamedBareBitNot.writtenContext prepared (actualContext .word)) checked.catalog.definitions ∧
      CoreProof.ContinuationAgreement (actual .word) [.inRight .unit (.word seven)] (certified.expression.rename embedding)
        (slots ++ actual .word) finalStore (shift 7 (next.rename embedding)) := by
  have empty : HeapRepresents checked compilation.registry (noFunctions checked.catalog) [] [] ⟨[]⟩ [] := GenericHeap.HeapRepresents.empty
  obtain ⟨heaps, ref⟩ := empty.allocate (GenericHeap.CellRepresents.initialized (ValueRep.word seven)) Dynamic.Heap.Allocates.append
  have environments : DataHeap.EnvRepresents (storageCatalog checked.catalog) [0] world [.function .unit .word]
      (scope .word) sourceEnvironment (canonical .word) := .cons ref (.nil (.cons readerTyped .nil))
  exact CompatibleRenamedBareBitNot.preserves_prefix_of_lower writable rfl (.inl rfl) observations environments heaps
    (localAgrees (some (.word seven))) (agrees .word) actualTyped
    (CompatiblePlaceCompilerCertificates.lower_of_lowerChecked accepted) sourceUpdate

private def exercise (raw : TypeSystem.Ty) (type : Core.Ty) (initial expected : Value) (succeeds : Bool) : IO Unit := do
  match compile raw type with
  | .error error => throw (IO.userError s!"renamed bare bit-not compile: {reprStr error}")
  | .ok certified =>
    let code := certified.expression.rename embedding
    let start := State.initial code (actual type) [initial]
    let wanted := if succeeds then Value.inRight .word expected else .inLeft type (.word invalid)
    let after := [if succeeds then .inRight .unit expected else initial]
    unless runStateful 2000 start == .done wanted after do throw (IO.userError "renamed bare bit-not captured continuation mismatch")
    for budget in [0, 7, 43] do
      match runStateful budget start with
      | .outOfFuel checkpoint => unless runStateful 2000 checkpoint == .done wanted after do
          throw (IO.userError "renamed bare bit-not captured resume mismatch")
      | .done value store => unless value == wanted && store == after do throw (IO.userError "renamed bare bit-not early completion mismatch")
      | .fault _ _ => throw (IO.userError "renamed bare bit-not stuck")
  -- Absence must also skip a continuation which would write the captured root.
  let effect := Expr.letE (.storeCell (.var 0) (.inRight .unit (if type = .integer then .integer 99 else .word (Word.ofNatModulo 99)))) (shift 1 next)
  match compile raw type effect with
  | .error error => throw (IO.userError s!"renamed bare bit-not effect compile: {reprStr error}")
  | .ok certified =>
    let absent := Value.inLeft type .unit
    unless runStateful 2000 (State.initial (certified.expression.rename embedding) (actual type) [absent]) ==
        .done (.inLeft type (.word invalid)) [absent] do throw (IO.userError "renamed absent operand ran captured write")

def run : IO Unit := do
  match accepted : compile .word .word with
  | .error error => throw (IO.userError s!"renamed bare bit-not Word compile: {reprStr error}")
  | .ok certified =>
    have _absent := actual_absent accepted
    have _prefix := actual_preserves_prefix accepted
    match ran : runStateful 2000 (State.initial (certified.expression.rename embedding) (actual .word) [.inRight .unit (.word seven)]) with
    | .done result after =>
      have _source := actual_reflects accepted (.initialized (.word seven)) (runStateful_evaluation_sound ran)
      unless result == .inRight .word (.word seven.bitNot) && after == [.inRight .unit (.word seven.bitNot)] do
        throw (IO.userError "renamed bare bit-not proof consumer mismatch")
    | _ => throw (IO.userError "renamed bare bit-not proof consumer incomplete")
  exercise .word .word (.inLeft .word .unit) (.word Word.zero) false
  exercise .word .word (.inRight .unit (.word seven)) (.word seven.bitNot) true
  -- Integer is an existing retained IR profile; source admission is unchanged.
  exercise .integer .integer (.inLeft .integer .unit) (.integer 0) false
  for value in [0, 7, -7, -(2^300 : Int)] do
    exercise .integer .integer (.inRight .unit (.integer value)) (.integer (~~~value)) true
  IO.println "renamed bare bit-not: independent writes/faults, Unit RHS, seven typed slots, existing closure capture and resume GREEN"

end Tests.SourceCoreCompatibleRenamedBareBitNot
