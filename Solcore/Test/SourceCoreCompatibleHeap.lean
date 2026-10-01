import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceKeys

#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! The compatible profile uses the existing allocation/write/frame laws,
including a nonidentity source/native location map. Raw staged mapping headers
survive actual encoding, registry extension, and the new key-vector adapter. -/
set_option autoImplicit false
set_option maxRecDepth 8192
namespace Tests.SourceCoreCompatibleHeap
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute
open SourceCoreCompatibleDataPlaces CompatiblePlaceKeys

private theorem except_get {α ε : Type} (result : Except ε α) (positive : result.toOption.isSome = true) :
    result = .ok (result.toOption.get positive) := by
  cases result with | error => simp [Except.toOption] at positive | ok => rfl
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def rootType : TypeSystem.Ty := .mapping .bool .word
private theorem preparedExists : (SourceCoreCompatibleCatalog.prepare signatures 100 [rootType, .proxy .word]).toOption.isSome = true := by cbv
private def checked := (SourceCoreCompatibleCatalog.prepare signatures 100 [rootType, .proxy .word]).toOption.get preparedExists
private def context := SourceCoreCompatibleValues.Context.initial checked
private def noFunctions (catalog : SourceCoreCompatibleCatalog.Catalog) : FunctionModel catalog where
  Represents := fun _ _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  source_function := False.elim
  extend := fun impossible _ _ _ => False.elim impossible
private def w (n : Nat) : Word := Word.ofNatModulo n
private def carrier : SourceCoreDataValues.Value := .mapping (.comptime .bool) .word [(.bool true, .word (w 7)), (.bool true, .word (w 9))]
private def sourceRoot : Dynamic.Value := .mapping (.comptime .bool) .word [(.bool true, .word (w 7)), (.bool true, .word (w 9))]
private theorem meaning : CompatibleEncoding.Means carrier sourceRoot :=
  .mapping (.prepend (.bool _) (.word _) (.prepend (.bool _) (.word _) .empty))

/-- This profile really differs from strict projection; only its registered
native definitions are shared by the heap adapter. -/
example : checked.catalog.project rootType ≠ (Except.mapError SourceCoreCompatibleCatalog.Error.catalog
    ((storageCatalog checked.catalog).project rootType)) := by cbv; intro impossible; cases impossible

private theorem allocate_encoded {encoded : SourceCoreCompatibleValues.Encoded 100 context rootType carrier}
    (accepted : SourceCoreCompatibleValues.encode 100 context rootType carrier = .ok encoded) :
    HeapRepresents checked encoded.context.registry (noFunctions checked.catalog) [1]
      [.integer, OptionalCell.cellType encoded.type] ⟨[⟨rootType, some sourceRoot, none⟩]⟩ [.integer (-123), .inRight .unit encoded.value] ∧
      ReferenceRepresents [1] [.integer, OptionalCell.cellType encoded.type] ⟨0⟩ 1 encoded.type := by
  have empty : HeapRepresents checked encoded.context.registry (noFunctions checked.catalog) [] [] ⟨[]⟩ [] :=
    GenericHeap.HeapRepresents.empty
  have administrative := empty.allocate_administrative (RuntimeValueHasType.integer (value := -123))
  have represented := CompatibleEncoding.encode_represents_at (functions := noFunctions checked.catalog) accepted meaning [] [.integer]
  exact administrative.allocate (.initialized represented) .append

private theorem writes_preserve_raw_header {encoded : SourceCoreCompatibleValues.Encoded 100 context rootType carrier}
    (accepted : SourceCoreCompatibleValues.encode 100 context rootType carrier = .ok encoded) :
    ∃ updated,
      Store.write? [.integer (-123), .inRight .unit encoded.value] 1 (.inRight .unit encoded.value) = some updated ∧
      HeapRepresents checked encoded.context.registry (noFunctions checked.catalog) [1]
        [.integer, OptionalCell.cellType encoded.type] ⟨[⟨rootType, some sourceRoot, none⟩]⟩ updated ∧
      AdministrativePreserved [1] [.integer (-123), .inRight .unit encoded.value] [1] updated := by
  obtain ⟨heaps, reference⟩ := allocate_encoded accepted
  have represented := CompatibleEncoding.encode_represents_at (functions := noFunctions checked.catalog) accepted meaning [1]
    [.integer, OptionalCell.cellType encoded.type]
  exact heaps.write_initialized reference (.intro .head) represented (.intro (.intro .head) .head)

private theorem registry_transport {encoded : SourceCoreCompatibleValues.Encoded 100 context rootType carrier}
    (accepted : SourceCoreCompatibleValues.encode 100 context rootType carrier = .ok encoded)
    {future : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends encoded.context.registry future) :
    HeapRepresents checked future (noFunctions checked.catalog) [1]
      [.integer, OptionalCell.cellType encoded.type] ⟨[⟨rootType, some sourceRoot, none⟩]⟩ [.integer (-123), .inRight .unit encoded.value] :=
  (allocate_encoded accepted).1.extend_registry extension

/-- A staged type view is transported at the source level before native key
slots are equated. The same key adapter consumes the generic sequence result. -/
example {source : TypedSource} {site : SourceCoreElaboration.ErrorSite} {key : ExpressionId}
    {steps : List PreparedStep} {sites : List (ExpressionId × Ty)}
    (path : PreparedPath checked source site rootType [.index key] 0 steps sites .word)
    (registry : SourceCoreRawMetadata.Registry) :
    ∃ _views : KeyViews path [.comptime .bool],
      Arguments checked registry (noFunctions checked.catalog) [] [] source site [.bool true] path [.index (.bool true)] := by
  cases path with
  | index certificate generated tail =>
    have shape := TypeSystem.Ty.mapping.inj certificate.view
    obtain ⟨rfl, rfl⟩ := shape
    cases tail
    have views : KeyViews (site := site) (.index certificate generated .nil) [.comptime .bool] :=
      .index (certificate := certificate) (generated := generated) (tail := .nil (site := site)) rfl .nil
    refine ⟨views, ?_⟩
    apply views.arguments (.index .nil)
      (DataExpressionSequence.Values.cons (show ValueRep checked registry (noFunctions checked.catalog) [] [] (.comptime .bool) (.bool true) (.bool true) .bool from .compatible (actual := .bool) rfl (.bool true)) .nil)
    intro index value found
    simpa only [Nat.zero_add] using found

def run : IO Unit := do
  match accepted : SourceCoreCompatibleValues.encode 100 context rootType carrier with
  | .error error => throw (IO.userError s!"compatible heap encode failed: {reprStr error}")
  | .ok encoded =>
    have _allocated := allocate_encoded accepted
    have _written := writes_preserve_raw_header accepted
    match SourceCoreCompatibleValues.encode 100 encoded.context (.proxy .word) (.proxy (.comptime .word)) with
    | .error error => throw (IO.userError s!"compatible heap registry extension failed: {reprStr error}")
    | .ok extra =>
      have _transported := registry_transport accepted extra.preserves
      let before := [Value.integer (-123), Value.inRight .unit encoded.value]
      match runStateful 20 (.initial (.loadCell (.var 0)) [.cellRef (OptionalCell.cellType encoded.type) 1] before) with
      | .done (.inRight .unit value) after =>
        unless after == before do throw (IO.userError "compatible heap load wrote a cell")
        match SourceCoreCompatibleValues.decode 100 extra.context rootType value with
        | .ok decoded => unless decoded == carrier do throw (IO.userError "compatible heap lost raw header or duplicate order")
        | .error error => throw (IO.userError s!"compatible heap decode failed: {reprStr error}")
      | other => throw (IO.userError s!"compatible heap live read failed: {reprStr other}")
  IO.println "compatible generic heap and key adapter GREEN"

end Tests.SourceCoreCompatibleHeap
