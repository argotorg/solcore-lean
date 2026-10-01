import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaValues

/-! Lambda formation at the actual generated syntax, including arbitrary
administrative insertions. The newly captured value is kept exactly as created.
Finite completion reflection follows from this direct evaluation, not from an
equality between closures captured in different environments. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaValues
open Core Frontend SourceInference GeneralHeap CompatiblePayload
open CallableIndexedHistory

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {actual : Core.Environment}

/-- The source location selected by a capture remains the same actual native
cell through the real embedding, including aliases. -/
theorem Captures.lookup (captured : Captures prepared mapping world scope function.captured actual)
    {binder : Resolved.LocalId} {location : Dynamic.Location}
    (found : Dynamic.Environment.LooksUp function.captured binder location) :
    ∃ index payload target, SourceCoreLocalCell.lookup? scope binder = some (index, payload) ∧
      actual[captured.embedding index]? = some (.cellRef (OptionalCell.cellType payload) target) ∧
      ReferenceRepresents mapping world location target payload := by
  obtain ⟨index, payload, target, selected, reference, represented⟩ := captured.represented.lookup_source found
  exact ⟨index, payload, target, selected, captured.agrees reference, represented⟩

theorem formation_evaluates
    (captured : Captures prepared mapping world scope function.captured actual)
    (code : Code prepared function scope captured.administrative) (history : History code)
    {store : Store} {location : Location}
    (reference : captured.canonical[code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location))
    (read : store.read? location = some (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame history.native)) :
    Evaluates actual store (code.lowered.expression.rename captured.embedding)
      (.inRight .word (value code captured.embedding history.native actual)) store := by
  rw [code.emitted]
  exact .inRight (.pair (.pair (.inLeft .unit) (.letE (.loadCell (.var (captured.agrees reference)) read) .lambda)) .word)

/-- The actual emitted expression and store determine native output typing.
No future world is invented for a read-only formation step. -/
theorem formation_represents
    (captured : Captures prepared mapping world scope function.captured actual)
    (code : Code prepared function scope captured.administrative) (history : History code)
    {store : Store} {location : Location}
    (stored : RuntimeStoreHasTypes world store prepared.layouts.definitions)
    (reference : captured.canonical[code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location))
    (read : store.read? location = some (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame history.native)) :
    Represents prepared mapping world (FunctionValues.sourceType function) (.closure function)
      (value code captured.embedding history.native actual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) := by
  have evaluated := formation_evaluates captured code history reference read
  obtain ⟨future, _, finalStored, resultTyped⟩ :=
    evaluation_preserves_type evaluated (code.typed.rename captured.respects) captured.typed stored
  have same : future = world := finalStored.world_eq.trans stored.world_eq.symm
  subst future
  cases resultTyped with
  | inRight typed => exact .lambda captured code history typed

/-- Source formation stores exactly the caller's raw source, context, evidence
and abstract capture locations. These are semantic inputs, not decoded guesses
from a native descriptor. No body execution is involved. -/
theorem source_formation {administrative : Core.Context}
    (code : Code prepared function scope administrative) (program : Program) (heap : Dynamic.Heap)
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    Dynamic.ExpressionEvaluates program function.context function.evidence function.source function.captured heap
      code.id (.closure function) heap := by
  apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound code.sourceFound)
  · rw [code.sourceForm]
    exact .lambda ordinary
  · rw [coercions]
    exact .nil

theorem formation
    (captured : Captures prepared mapping world scope function.captured actual)
    (code : Code prepared function scope captured.administrative) (history : History code)
    (program : Program) (heap : Dynamic.Heap)
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = [])
    {store : Store} {location : Location}
    (stored : RuntimeStoreHasTypes world store prepared.layouts.definitions)
    (reference : captured.canonical[code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location))
    (read : store.read? location = some (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame history.native)) :
    Dynamic.ExpressionEvaluates program function.context function.evidence function.source function.captured heap
      code.id (.closure function) heap ∧
    Evaluates actual store (code.lowered.expression.rename captured.embedding)
      (.inRight .word (value code captured.embedding history.native actual)) store ∧
    Represents prepared mapping world (FunctionValues.sourceType function) (.closure function)
      (value code captured.embedding history.native actual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) :=
  ⟨source_formation code program heap ordinary coercions,
    formation_evaluates captured code history reference read,
    formation_represents captured code history stored reference read⟩

theorem reflects
    (captured : Captures prepared mapping world scope function.captured actual)
    (code : Code prepared function scope captured.administrative) (history : History code)
    (program : Program) (heap : Dynamic.Heap)
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = [])
    {before after : Store} {location : Location} {result : Core.Value}
    (stored : RuntimeStoreHasTypes world before prepared.layouts.definitions)
    (reference : captured.canonical[code.referenceIndex]? = some (.cellRef prepared.ancestry.layout.frame.type location))
    (read : before.read? location = some (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame history.native))
    (completed : Evaluates actual before (code.lowered.expression.rename captured.embedding) result after) :
    result = .inRight .word (value code captured.embedding history.native actual) ∧ after = before ∧
    Dynamic.ExpressionEvaluates program function.context function.evidence function.source function.captured heap
      code.id (.closure function) heap ∧
    Represents prepared mapping world (FunctionValues.sourceType function) (.closure function)
      (value code captured.embedding history.native actual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) := by
  obtain ⟨source, native, related⟩ := formation captured code history program heap ordinary coercions stored reference read
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed native
  exact ⟨rfl, rfl, source, related⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaValues
