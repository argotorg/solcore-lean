import Solcore.SourceSemantics.CoreLowering.Internal.Data.Payloads
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.LiteralsAndStagedValues
import Solcore.Frontend.SourceCore.DataPlaces
import Solcore.SourceSemantics.Dynamic.Fault
import Solcore.SourceSemantics.CoreLowering.Internal.Data.PlaceExecution
import Solcore.SourceSemantics.CoreLowering.Internal.Data.PlaceMappings

/-!
# Data: place reflection

Reflection of place getters, setters, modifiers, commits and continuations, and the success of assignments.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataPlaceModifier
/-! The actual place modifier succeeds on initialized, equally typed numeric
operands. This is the condition needed when Core computes the modifier before
the latest-root traversal: no operand fault can preempt a structural fault.
Uninitialized snapshots remain an explicit separate case. Unchecked `/=` and
`%=` compute a total operation here; their panic on a zero right operand is
checked after the structural update, by `SourceCoreDataPlaces.guard`. The
independent bit-not-assignment relation currently admits Word only. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlaceModifier
open Core Frontend Frontend.SourceInference SourceCoreDataPlaces DataEquality GeneralHeap DataPayload

theorem assignment_excludes_invalid {operator : Syntax.ValueAssignOp}
    {snapshot : Option Dynamic.Value} {right result : Dynamic.Value}
    (applied : Dynamic.AssignmentValueApplies operator snapshot right result) :
    ¬ Dynamic.AssignmentOperandsInvalid operator snapshot right := by
  intro invalid
  cases invalid with
  | uninitialized different => cases applied; exact different rfl
  | compound corresponds invalid =>
    cases corresponds <;> cases applied <;>
      exact invalid.excludes_application ⟨_, by assumption⟩

/-- An applied compound assignment has a nonzero divisor whenever it may panic. -/
theorem assignment_divisor {operator : Syntax.ValueAssignOp}
    {snapshot : Option Dynamic.Value} {right result : Dynamic.Value}
    (applied : Dynamic.AssignmentValueApplies operator snapshot right result) :
    operator.mayPanic = false ∨ right ≠ .word Word.zero := by
  cases applied with
  | uncheckedDivide applies =>
    cases applies with
    | wordUncheckedDivide _ _ nonzero => exact .inr fun same => nonzero (Dynamic.Value.word.inj same)
  | uncheckedModulo applies =>
    cases applies with
    | wordUncheckedModulo _ _ nonzero => exact .inr fun same => nonzero (Dynamic.Value.word.inj same)
  | _ => exact .inl rfl

/-- A panicking operator meets the operator profile at Word leaves only. -/
theorem panicking_word {operator : Syntax.ValueAssignOp} {sourceType : TypeSystem.Ty}
    (profile : operator = .equal ∨ sourceType = .word ∨ sourceType = .integer ∧ operator.wordOnly = false)
    (panics : operator.mayPanic = true) : sourceType = .word := by
  rcases profile with same | word | ⟨_, notWordOnly⟩
  · subst same; simp [Syntax.ValueAssignOp.mayPanic] at panics
  · exact word
  · cases operator <;> simp_all [Syntax.ValueAssignOp.mayPanic, Syntax.ValueAssignOp.wordOnly]

/-- A Word-typed representation relates a source Word to the same Core Word. -/
theorem word_rep {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel catalog} {mapping : LocationMap} {world : StoreTyping}
    {source : Dynamic.Value} {core : Value} {type : Ty}
    (related : ValueRep catalog signatures functions mapping world .word source core type) :
    ∃ word, source = .word word ∧ core = .word word := by
  cases related with
  | word word => exact ⟨word, rfl, rfl⟩
  | constructed nominal => simp [SourceCoreDataCatalog.nominalParts, TypeSystem.Ty.word] at nominal

/-- Only unchecked `/=` and `%=` select a panicking modifier. -/
theorem binaryOperator_panics {integer : Bool} {operator : Syntax.ValueAssignOp} {operation : BinaryOp}
    (selected : binaryOperator integer operator = some ⟨operation, true⟩) : operator.mayPanic = true := by
  cases operator <;> first | rfl | simp [binaryOperator, Modifier.total] at selected

/-- An applied source operation passes the check of its modifier. -/
theorem passes_of_applies {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel catalog} {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {type : Ty} {operator : Syntax.ValueAssignOp}
    {snapshot : Option Dynamic.Value} {right result : Dynamic.Value} {rightCore : Value}
    (profile : operator = .equal ∨ sourceType = .word ∨ sourceType = .integer ∧ operator.wordOnly = false)
    (rightRep : ValueRep catalog signatures functions mapping world sourceType right rightCore type)
    (applies : Dynamic.AssignmentValueApplies operator snapshot right result) (integer : Bool) :
    Passes (binaryOperator integer operator) rightCore := by
  by_cases panics : operator.mayPanic = true
  · have word := panicking_word profile panics
    subst word
    obtain ⟨word, rfl, rfl⟩ := word_rep rightRep
    rcases assignment_divisor applies with total | different
    · rw [panics] at total; cases total
    · have nonzero : word ≠ Word.zero := fun same => different (same ▸ rfl)
      cases operator <;> simp [Syntax.ValueAssignOp.mayPanic] at panics
      · exact .nonzero nonzero
      · exact .nonzero nonzero
  · apply Passes.total
    intro modifier selected
    cases operator <;> simp only [binaryOperator, Modifier.total, Option.some.injEq, reduceCtorEq] at selected <;>
      first | (subst selected; rfl) | simp [Syntax.ValueAssignOp.mayPanic] at panics

/-- A panicking compound assignment has no invalid operands. -/
theorem panic_excludes_invalid {operator : Syntax.ValueAssignOp}
    {snapshot : Option Dynamic.Value} {right : Dynamic.Value} {code : UInt8}
    (panics : Dynamic.AssignmentOperandsPanic operator snapshot right code) :
    ¬ Dynamic.AssignmentOperandsInvalid operator snapshot right := by
  intro invalid
  cases panics with
  | compound corresponds panics =>
    cases invalid with
    | compound other invalid =>
      cases corresponds <;> cases other <;> exact invalid.excludes_panic panics

theorem assignment_functional {operator : Syntax.ValueAssignOp}
    {snapshot : Option Dynamic.Value} {right first second : Dynamic.Value}
    (left : Dynamic.AssignmentValueApplies operator snapshot right first)
    (rightApplication : Dynamic.AssignmentValueApplies operator snapshot right second) : first = second := by
  cases left <;> cases rightApplication <;> first
    | rfl
    | exact Dynamic.BinaryPrimitiveApplies.functional (by assumption) (by assumption)

private theorem binary_modified {type : Ty} {modifier : Modifier}
    {environment : Environment} {snapshot rhs : Expr} {left right result : Value}
    (applied : modifier.operation.apply left right = some result)
    (snapshotSelected : Selects environment snapshot (.inRight .unit left))
    (rightSelected : Selects environment rhs right) (store : Store) (invalid : Word) :
    Evaluates environment store (modified type (some modifier) false snapshot rhs invalid)
      (.inRight .word result) store :=
  .caseRight (snapshotSelected.evaluates store)
    (.inRight (.binary (.var rfl) ((rightSelected.weaken left).evaluates store) applied))

theorem equal_modified {type : Ty} {environment : Environment} {snapshot rhs : Expr} {right : Value}
    (selected : Selects environment rhs right) (store : Store) (invalid : Word) :
    Evaluates environment store (modified type none false snapshot rhs invalid) (.inRight .word right) store :=
  .inRight (selected.evaluates store)

theorem word_success (operator : Syntax.ValueAssignOp) (left right : Word)
    (divisor : operator.mayPanic = false ∨ right ≠ Word.zero)
    {environment : Environment} {snapshot rhs : Expr}
    (snapshotSelected : Selects environment snapshot (.inRight .unit (.word left)))
    (rightSelected : Selects environment rhs (.word right)) (store : Store) (invalid : Word) :
    ∃ result : Word, Dynamic.AssignmentValueApplies operator (some (.word left)) (.word right) (.word result) ∧
      Evaluates environment store (modified .word (binaryOperator false operator) false snapshot rhs invalid)
        (.inRight .word (.word result)) store := by
  cases operator with
  | equal => exact ⟨right, .equal _ _, equal_modified rightSelected store invalid⟩
  | add => exact ⟨_, .add (.wordAdd left right), binary_modified rfl snapshotSelected rightSelected store invalid⟩
  | subtract => exact ⟨_, .subtract (.wordSubtract left right), binary_modified rfl snapshotSelected rightSelected store invalid⟩
  | multiply => exact ⟨_, .multiply (.wordMultiply left right), binary_modified rfl snapshotSelected rightSelected store invalid⟩
  | divide => exact ⟨_, .divide (.wordDivide left right), binary_modified rfl snapshotSelected rightSelected store invalid⟩
  | modulo => exact ⟨_, .modulo (.wordModulo left right), binary_modified rfl snapshotSelected rightSelected store invalid⟩
  | bitAnd => exact ⟨_, .bitAnd (.wordBitAnd left right), binary_modified rfl snapshotSelected rightSelected store invalid⟩
  | bitOr => exact ⟨_, .bitOr (.wordBitOr left right), binary_modified rfl snapshotSelected rightSelected store invalid⟩
  | bitXor => exact ⟨_, .bitXor (.wordBitXor left right), binary_modified rfl snapshotSelected rightSelected store invalid⟩
  | shiftLeft => exact ⟨_, .shiftLeft (.wordShiftLeft left right), binary_modified rfl snapshotSelected rightSelected store invalid⟩
  | shiftRight => exact ⟨_, .shiftRight (.wordShiftRight left right), binary_modified rfl snapshotSelected rightSelected store invalid⟩
  | uncheckedAdd => exact ⟨_, .uncheckedAdd (.wordUncheckedAdd left right), binary_modified rfl snapshotSelected rightSelected store invalid⟩
  | uncheckedSubtract => exact ⟨_, .uncheckedSubtract (.wordUncheckedSubtract left right), binary_modified rfl snapshotSelected rightSelected store invalid⟩
  | uncheckedMultiply => exact ⟨_, .uncheckedMultiply (.wordUncheckedMultiply left right), binary_modified rfl snapshotSelected rightSelected store invalid⟩
  | uncheckedDivide =>
    have nonzero := divisor.resolve_left (by decide)
    exact ⟨_, .uncheckedDivide (.wordUncheckedDivide left right nonzero),
      binary_modified rfl snapshotSelected rightSelected store invalid⟩
  | uncheckedModulo =>
    have nonzero := divisor.resolve_left (by decide)
    exact ⟨_, .uncheckedModulo (.wordUncheckedModulo left right nonzero),
      binary_modified rfl snapshotSelected rightSelected store invalid⟩

/-- Every compound operator but the shifts and the unchecked arithmetic, which
take Words only, has an Integer form. -/
theorem integer_success (operator : Syntax.ValueAssignOp) (notWordOnly : operator.wordOnly = false) (left right : Int)
    {environment : Environment} {snapshot rhs : Expr}
    (snapshotSelected : Selects environment snapshot (.inRight .unit (.integer left)))
    (rightSelected : Selects environment rhs (.integer right)) (store : Store) (invalid : Word) :
    ∃ result : Int, Dynamic.AssignmentValueApplies operator (some (.integer left)) (.integer right) (.integer result) ∧
      Evaluates environment store (modified .integer (binaryOperator true operator) false snapshot rhs invalid)
        (.inRight .word (.integer result)) store := by
  cases operator with
  | equal => exact ⟨right, .equal _ _, equal_modified rightSelected store invalid⟩
  | add => exact ⟨_, .add (.integerAdd left right), binary_modified rfl snapshotSelected rightSelected store invalid⟩
  | subtract => exact ⟨_, .subtract (.integerSubtract left right), binary_modified rfl snapshotSelected rightSelected store invalid⟩
  | multiply => exact ⟨_, .multiply (.integerMultiply left right), binary_modified rfl snapshotSelected rightSelected store invalid⟩
  | divide => exact ⟨_, .divide (IntegerPrimitives.divide_source left right), binary_modified rfl snapshotSelected rightSelected store invalid⟩
  | modulo => exact ⟨_, .modulo (IntegerPrimitives.modulo_source left right), binary_modified rfl snapshotSelected rightSelected store invalid⟩
  | bitAnd => exact ⟨_, .bitAnd (IntegerPrimitives.bitAnd_source left right), binary_modified rfl snapshotSelected rightSelected store invalid⟩
  | bitOr => exact ⟨_, .bitOr (IntegerPrimitives.bitOr_source left right), binary_modified rfl snapshotSelected rightSelected store invalid⟩
  | bitXor => exact ⟨_, .bitXor (IntegerPrimitives.bitXor_source left right), binary_modified rfl snapshotSelected rightSelected store invalid⟩
  | shiftLeft | shiftRight | uncheckedAdd | uncheckedSubtract | uncheckedMultiply
  | uncheckedDivide | uncheckedModulo =>
    simp [Syntax.ValueAssignOp.wordOnly] at notWordOnly

/-- Full authenticated payloads at Word/Integer type expose the matching
primitive values. No source execution or Core modifier evaluation is assumed. -/
theorem initialized_success {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel catalog} {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {type : Ty} {left right : Dynamic.Value} {leftCore rightCore : Value}
    {operator : Syntax.ValueAssignOp} (numeric : sourceType = .word ∨ sourceType = .integer ∧ operator.wordOnly = false)
    (divisor : operator.mayPanic = false ∨ right ≠ .word Word.zero)
    (leftRep : ValueRep catalog signatures functions mapping world sourceType left leftCore type)
    (rightRep : ValueRep catalog signatures functions mapping world sourceType right rightCore type)
    {environment : Environment} {snapshot rhs : Expr}
    (snapshotSelected : Selects environment snapshot (.inRight .unit leftCore))
    (rightSelected : Selects environment rhs rightCore) (store : Store) (invalid : Word) :
    ∃ result value, ValueRep catalog signatures functions mapping world sourceType result value type ∧
      Dynamic.AssignmentValueApplies operator (some left) right result ∧
      Evaluates environment store (modified type (binaryOperator (type = .integer) operator) false snapshot rhs invalid)
        (.inRight .word value) store ∧ ¬ Dynamic.AssignmentOperandsInvalid operator (some left) right := by
  rcases numeric with rfl | ⟨rfl, notWordOnly⟩
  · cases leftRep with
    | word left =>
      cases rightRep with
      | word right =>
        obtain ⟨result, source, core⟩ := word_success operator left right
          (divisor.imp_right fun different same => different (congrArg Dynamic.Value.word same))
          snapshotSelected rightSelected store invalid
        exact ⟨_, _, .word result, source, core, assignment_excludes_invalid source⟩
    | constructed nominal => simp [SourceCoreDataCatalog.nominalParts, TypeSystem.Ty.word] at nominal
  · cases leftRep with
    | integer left =>
      cases rightRep with
      | integer right =>
        obtain ⟨result, source, core⟩ := integer_success operator notWordOnly left right snapshotSelected rightSelected store invalid
        exact ⟨_, _, .integer result, source, core, assignment_excludes_invalid source⟩
    | constructed nominal => simp [SourceCoreDataCatalog.nominalParts, TypeSystem.Ty.integer] at nominal

/-- Preserve an independently chosen source assignment result. Its equality
with the total primitive result follows from the source rules themselves. -/
theorem initialized_preserves {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel catalog} {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {type : Ty} {left right result : Dynamic.Value} {leftCore rightCore : Value}
    {operator : Syntax.ValueAssignOp} (numeric : sourceType = .word ∨ sourceType = .integer ∧ operator.wordOnly = false)
    (leftRep : ValueRep catalog signatures functions mapping world sourceType left leftCore type)
    (rightRep : ValueRep catalog signatures functions mapping world sourceType right rightCore type)
    (source : Dynamic.AssignmentValueApplies operator (some left) right result)
    {environment : Environment} {snapshot rhs : Expr}
    (snapshotSelected : Selects environment snapshot (.inRight .unit leftCore))
    (rightSelected : Selects environment rhs rightCore) (store : Store) (invalid : Word) :
    ∃ value, ValueRep catalog signatures functions mapping world sourceType result value type ∧
      Evaluates environment store (modified type (binaryOperator (type = .integer) operator) false snapshot rhs invalid)
        (.inRight .word value) store ∧ ¬ Dynamic.AssignmentOperandsInvalid operator (some left) right := by
  obtain ⟨result', value, represented, generated, evaluated, valid⟩ :=
    initialized_success numeric (assignment_divisor source) leftRep rightRep snapshotSelected rightSelected store invalid
  have same := assignment_functional generated source
  subst result'
  exact ⟨value, represented, evaluated, valid⟩

/-- Unchecked `/=` and `%=` on a Word leaf and a zero right operand: the
source panics with `0x12`, while Core's total modifier gives a Word and its
panicking modifier fails later, in `SourceCoreDataPlaces.guard`. -/
theorem initialized_panic {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel catalog} {mapping : LocationMap} {world : StoreTyping}
    {type : Ty} {left : Dynamic.Value} {leftCore : Value}
    {operator : Syntax.ValueAssignOp} (panics : operator.mayPanic = true)
    (leftRep : ValueRep catalog signatures functions mapping world .word left leftCore type)
    {environment : Environment} {snapshot rhs : Expr}
    (snapshotSelected : Selects environment snapshot (.inRight .unit leftCore))
    (rightSelected : Selects environment rhs (.word Word.zero)) (store : Store) (invalid : Word) :
    ∃ changed value operation,
      ValueRep catalog signatures functions mapping world .word changed value type ∧
      binaryOperator (type = .integer) operator = some ⟨operation, true⟩ ∧
      Dynamic.AssignmentOperandsPanic operator (some left) (.word Word.zero) SourceCorePanics.divisionByZero ∧
      Evaluates environment store (modified type (binaryOperator (type = .integer) operator) false snapshot rhs invalid)
        (.inRight .word value) store ∧
      ¬ Dynamic.AssignmentOperandsInvalid operator (some left) (.word Word.zero) := by
  cases leftRep with
  | word left =>
    cases operator with
    | uncheckedDivide =>
      have panicked : Dynamic.AssignmentOperandsPanic .uncheckedDivide (some (.word left)) (.word Word.zero)
          SourceCorePanics.divisionByZero := .compound .uncheckedDivide (.wordUncheckedDivide left)
      exact ⟨_, _, _, .word (left.udiv Word.zero), rfl, panicked,
        binary_modified rfl snapshotSelected rightSelected store invalid, panic_excludes_invalid panicked⟩
    | uncheckedModulo =>
      have panicked : Dynamic.AssignmentOperandsPanic .uncheckedModulo (some (.word left)) (.word Word.zero)
          SourceCorePanics.divisionByZero := .compound .uncheckedModulo (.wordUncheckedModulo left)
      exact ⟨_, _, _, .word (left.umod Word.zero), rfl, panicked,
        binary_modified rfl snapshotSelected rightSelected store invalid, panic_excludes_invalid panicked⟩
    | _ => simp [Syntax.ValueAssignOp.mayPanic] at panics
  | constructed nominal => simp [SourceCoreDataCatalog.nominalParts, TypeSystem.Ty.word] at nominal

/-- Plain assignment does not inspect its previous snapshot and supports every
authenticated payload, including closures and mappings. -/
theorem equal_success {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel catalog} {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {type : Ty} {right : Dynamic.Value} {rightCore : Value}
    (rightRep : ValueRep catalog signatures functions mapping world sourceType right rightCore type)
    (previous : Option Dynamic.Value) {environment : Environment} {snapshot rhs : Expr}
    (rightSelected : Selects environment rhs rightCore) (store : Store) (invalid : Word) :
    ValueRep catalog signatures functions mapping world sourceType right rightCore type ∧
      Dynamic.AssignmentValueApplies .equal previous right right ∧
      Evaluates environment store (modified type (binaryOperator (type = .integer) .equal) false snapshot rhs invalid)
        (.inRight .word rightCore) store ∧ ¬ Dynamic.AssignmentOperandsInvalid .equal previous right :=
  ⟨rightRep, .equal _ _, equal_modified rightSelected store invalid, assignment_excludes_invalid (.equal _ _)⟩

theorem word_bitNot_success (value : Word) {environment : Environment} {snapshot rhs : Expr}
    (snapshotSelected : Selects environment snapshot (.inRight .unit (.word value)))
    (operator : Option Frontend.SourceCoreDataPlaces.Modifier) (store : Store) (invalid : Word) :
    Dynamic.BitNotSnapshot (some (.word value)) (.word value.bitNot) ∧
      Evaluates environment store (modified .word operator true snapshot rhs invalid)
        (.inRight .word (.word value.bitNot)) store ∧
      ¬ Dynamic.UnaryPrimitiveOperandInvalid .bitNot (.word value) := by
  refine ⟨.word value, .caseRight (snapshotSelected.evaluates store) (.inRight (.unary (.var rfl) rfl)), ?_⟩
  intro invalid
  exact invalid.excludes_application ⟨_, .wordBitNot value⟩

/-- Integer bit-not agrees with the unary primitive. The corresponding
snapshot-assignment constructor is connected in IntegerBitNotSnapshot. -/
theorem integer_bitNot_primitive (value : Int) {environment : Environment} {snapshot rhs : Expr}
    (snapshotSelected : Selects environment snapshot (.inRight .unit (.integer value)))
    (operator : Option Frontend.SourceCoreDataPlaces.Modifier) (store : Store) (invalid : Word) :
    Dynamic.UnaryPrimitiveApplies .bitNot (.integer value) (.integer (~~~value)) ∧
      Evaluates environment store (modified .integer operator true snapshot rhs invalid)
        (.inRight .word (.integer (~~~value))) store ∧
      ¬ Dynamic.UnaryPrimitiveOperandInvalid .bitNot (.integer value) := by
  refine ⟨.integerBitNot value, .caseRight (snapshotSelected.evaluates store) (.inRight (.unary (.var rfl) rfl)), ?_⟩
  intro invalid
  exact invalid.excludes_application ⟨_, .integerBitNot value⟩

/-- Once the initialized numeric premise is established, the modifier cannot
produce a language failure at any completed Core evaluation. -/
theorem no_failure {environment : Environment} {store after : Store} {expression : Expr} {value : Value}
    {type : Ty} {token : Word} (success : Evaluates environment store expression (.inRight .word value) store) :
    ¬ Evaluates environment store expression (.inLeft type (.word token)) after := by
  intro failed
  have impossible := (evaluation_deterministic success failed).1
  cases impossible

end Solcore.SourceSemantics.CoreLowering.DataPlaceModifier
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataPlaceAssignmentWriteBack
/-! The assignment writeback phase consumes the independent latest-root
update. It derives the setter, administrative extension and single mapped
write, including plain initialization of an absent bare root.
-/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlaceAssignmentWriteBack
open Core Frontend Frontend.SourceInference GeneralHeap DataPatternValues DataPayload
open SourceCoreDataPlaces DataPayloadReadPaths

/-- A source update with a snapshot-dependent modifier installs one fixed
replacement at the final leaf. This extraction preserves all intermediate
mapping lookups, defaults, insertions and constructor reconstruction. -/
theorem replacement_of_update {Modify : Dynamic.Value → Prop} {initial : Option Dynamic.Value}
    {projections : List Dynamic.EvaluatedProjection} {updated : Dynamic.Value}
    (changed : Dynamic.ProjectionsUpdate (fun _ value => Modify value) initial projections updated) :
    ∃ replacement, Modify replacement ∧
      Dynamic.ProjectionsUpdate (fun _ value => value = replacement) initial projections updated := by
  induction changed with
  | leaf modified => exact ⟨_, modified, .leaf rfl⟩
  | indexFound found _ inserted ih =>
    obtain ⟨replacement, modified, changed⟩ := ih
    exact ⟨replacement, modified, .indexFound found changed inserted⟩
  | indexDefault absent defaulted _ inserted ih =>
    obtain ⟨replacement, modified, changed⟩ := ih
    exact ⟨replacement, modified, .indexDefault absent defaulted changed inserted⟩
  | member selected _ replaced ih =>
    obtain ⟨replacement, modified, changed⟩ := ih
    exact ⟨replacement, modified, .member selected changed replaced⟩

private theorem empty_represents {checked : SourceCoreDataCatalog.Checked} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel checked.catalog} {mapping : LocationMap} {world : StoreTyping}
    {keys : List Value} {root leaf : TypeSystem.Ty} {type leafType : Ty} {steps : List PreparedStep} {count : Nat}
    (path : Path checked signatures functions mapping world keys root type steps [] leaf leafType count)
    {source : Dynamic.Value} {value : Value}
    (represented : ValueRep checked.catalog signatures functions mapping world leaf source value leafType) :
    ValueRep checked.catalog signatures functions mapping world root source value type := by
  generalize projectionsEq : ([] : List Dynamic.EvaluatedProjection) = projections at path
  induction path with
  | nil => exact represented
  | member => cases projectionsEq
  | index => cases projectionsEq
  | comptime _ ih => exact .comptime (ih represented projectionsEq)

theorem setter_evaluates {checked : SourceCoreDataCatalog.Checked} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel checked.catalog} {mapping : LocationMap} {world : StoreTyping}
    {identities : Dynamic.Value → Word → Prop}
    (observations : FunctionObservations checked.catalog signatures functions identities)
    (faithful : DataEquality.IdentityFaithful identities) (layouts : CatalogLayouts checked.catalog)
    (prepared : Prepared) {keys : List Value} (keyLength : prepared.keyTypes.length = keys.length)
    {cell : Dynamic.Cell} {optional replacement : Value} {initial : Option Dynamic.Value}
    {updatedSource replacementSource : Dynamic.Value} {leaf : TypeSystem.Ty}
    {projections : List Dynamic.EvaluatedProjection} {count : Nat}
    (rootLayout : DataPlaceSnapshot.RootLayout checked.catalog prepared cell.type)
    (cellRep : GenericHeap.CellRepresents (payloadModel checked.catalog signatures functions) mapping world
      cell optional prepared.route.rootType)
    (root : Dynamic.RootInitialValue cell initial)
    (changed : Dynamic.ProjectionsUpdate (fun _ value => value = replacementSource) initial projections updatedSource)
    (path : Path checked signatures functions mapping world keys cell.type prepared.route.rootType
      prepared.steps projections leaf prepared.route.leafType count)
    (replacementRep : ValueRep checked.catalog signatures functions mapping world leaf replacementSource replacement prepared.route.leafType)
    {environment : Environment} {before store : Store} {keyType : Ty} {argument : Expr}
    (argumentEvaluated : Evaluates environment before argument (.pair optional (.pair (packValues keys) replacement)) store) :
    ∃ updatedValue finalStore administrative,
      ValueRep checked.catalog signatures functions mapping world cell.type updatedSource updatedValue prepared.route.rootType ∧
      Evaluates environment before (.apply (setter prepared keyType) argument) (.inRight .word updatedValue) finalStore ∧
      finalStore = store ++ administrative ∧ administrative.length = 2 * count := by
  cases initial with
  | some source =>
    obtain ⟨value, normalized, represented⟩ := DataPlaceSnapshot.root_present rootLayout cellRep root
    exact DataPayloadWriteBack.setter_evaluates observations faithful layouts prepared keyLength path
      normalized represented replacementRep changed keyType argumentEvaluated
  | none =>
    cases changed with
    | leaf same =>
      subst updatedSource
      obtain ⟨empty, _, rfl⟩ := DataPlaceSnapshot.path_empty path
      exact ⟨replacement, store, [], empty_represents path replacementRep,
        .apply .lambda argumentEvaluated (by simp only [empty]; exact .inRight (.second (.second (.var rfl)))),
        by simp, rfl⟩

/-- No modifier, getter or setter runtime behavior is assumed. The actual
setter argument loads the current mapped root, and the source's own write
determines the final heap. The returned evaluation/write witnesses compose
directly with execute_success. -/
theorem preserves {checked : SourceCoreDataCatalog.Checked} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel checked.catalog} {mapping : LocationMap} {world : StoreTyping}
    {identities : Dynamic.Value → Word → Prop}
    (observations : FunctionObservations checked.catalog signatures functions identities)
    (faithful : DataEquality.IdentityFaithful identities) (layouts : CatalogLayouts checked.catalog)
    (prepared : Prepared) {keys : List Value} (keyLength : prepared.keyTypes.length = keys.length)
    {heap after : Dynamic.Heap} {store : Store} {sourceLocation : Dynamic.Location} {target : Location}
    {cell : Dynamic.Cell} {replacement : Value} {initial : Option Dynamic.Value}
    {updatedSource replacementSource : Dynamic.Value} {leaf : TypeSystem.Ty}
    {projections : List Dynamic.EvaluatedProjection} {count : Nat}
    (heaps : GenericHeap.HeapRepresents (payloadModel checked.catalog signatures functions) mapping world heap store)
    (reference : ReferenceRepresents mapping world sourceLocation target prepared.route.rootType)
    (read : Dynamic.Heap.Reads heap sourceLocation cell)
    (rootLayout : DataPlaceSnapshot.RootLayout checked.catalog prepared cell.type)
    (root : Dynamic.RootInitialValue cell initial)
    (changed : Dynamic.ProjectionsUpdate (fun _ value => value = replacementSource) initial projections updatedSource)
    (written : Dynamic.Heap.Writes heap sourceLocation (some updatedSource) after)
    (path : Path checked signatures functions mapping world keys cell.type prepared.route.rootType
      prepared.steps projections leaf prepared.route.leafType count)
    (replacementRep : ValueRep checked.catalog signatures functions mapping world leaf replacementSource replacement prepared.route.leafType)
    {environment : Environment} {context : Core.Context} {keyType : Ty} {referenceExpression keyExpression replacementExpression : Expr}
    (environmentTyped : RuntimeEnvironmentHasTypes world environment context checked.catalog.definitions)
    (helperTyped : HasType context
      (.apply (setter prepared keyType) (.pair (.loadCell referenceExpression) (.pair keyExpression replacementExpression)))
      (LanguageResult.resultType prepared.route.rootType) checked.catalog.definitions)
    (referenceSelected : DataEquality.Selects environment referenceExpression
      (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (keysSelected : DataEquality.Selects environment keyExpression (packValues keys))
    (replacementSelected : DataEquality.Selects environment replacementExpression replacement) :
    ∃ updatedValue helperStore finalStore futureWorld old,
      ValueRep checked.catalog signatures functions mapping futureWorld cell.type updatedSource updatedValue prepared.route.rootType ∧
      Evaluates environment store
        (.apply (setter prepared keyType) (.pair (.loadCell referenceExpression) (.pair keyExpression replacementExpression)))
        (.inRight .word updatedValue) helperStore ∧
      helperStore.read? target = some old ∧ helperStore.write? target (.inRight .unit updatedValue) = some finalStore ∧
      WorldExtends world futureWorld ∧
      GenericHeap.HeapRepresents (payloadModel checked.catalog signatures functions) mapping futureWorld after finalStore ∧
      AdministrativePreserved mapping store mapping finalStore ∧ Dynamic.HeapMetadataExtend heap after := by
  obtain ⟨optional, coreRead, cellRep⟩ := DataPlaceSnapshot.read_at heaps reference read
  have argument : Evaluates environment store (.pair (.loadCell referenceExpression) (.pair keyExpression replacementExpression))
      (.pair optional (.pair (packValues keys) replacement)) store :=
    .pair (.loadCell (referenceSelected.evaluates store) coreRead)
      (.pair (keysSelected.evaluates store) (replacementSelected.evaluates store))
  obtain ⟨updatedValue, helperStore, administrative, represented, evaluated, extended, _⟩ :=
    setter_evaluates observations faithful layouts prepared keyLength rootLayout cellRep root changed path replacementRep argument
  obtain ⟨futureWorld, extension, helperHeaps, _, frame⟩ :=
    DataMappingHeap.evaluation_preserves_frame heaps environmentTyped helperTyped evaluated extended
  have futureRep := represented.extend (.refl _) extension
  obtain ⟨finalStore, coreWritten, finalHeaps, writeFrame⟩ :=
    helperHeaps.write_initialized (reference.extend (.refl _) extension) read futureRep written
  have helperRead : helperStore.read? target = some optional := by
    rw [extended]
    simpa [Store.read?, List.getElem?_append_left (heaps.target_lt reference.mapped)] using coreRead
  exact ⟨updatedValue, helperStore, finalStore, futureWorld, optional, futureRep, evaluated,
    helperRead, coreWritten, extension, finalHeaps, frame.trans writeFrame, .of_write written⟩

end Solcore.SourceSemantics.CoreLowering.DataPlaceAssignmentWriteBack
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataPlaceGetterReflection
/-! Completed live-root getters reflect an independently constructed source
snapshot or failure. Uninitialized mappings are virtual empty values; ordinary
absent roots remain absent for a bare assignment and fail before a projection.
Only administrative Core cells are appended. No source evaluation trace or
child/helper execution is an assumption of the live-root reflection theorem. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlaceGetterReflection
open Core Frontend Frontend.SourceInference GeneralHeap DataPatternValues DataPayload
open SourceCoreDataPlaces DataPlaceRouteCertificates DataPlaceSnapshot DataEquality

/-- Source observations of the snapshot phase. The invalid-projection branch
records the independent absent root and nonempty path; missing-default reasons
retain their exact type-indexed diagnostic. -/
inductive ResultRep (catalog : SourceCoreDataCatalog.Catalog) (signatures : ProgramSignatures)
    (functions : GenericHeap.PayloadModel catalog) (mapping : LocationMap) (world : StoreTyping)
    (prepared : Prepared) (missing : TypeSystem.Ty → Word) (leaf : TypeSystem.Ty)
    (cell : Dynamic.Cell) (projections : List Dynamic.EvaluatedProjection) : Value → Prop where
  | read {initial selected : Option Dynamic.Value} {snapshot : Value}
      (root : Dynamic.RootInitialValue cell initial)
      (read : Dynamic.ProjectionsRead initial projections selected)
      (related : OptionalRep catalog signatures functions mapping world leaf prepared.route.leafType selected snapshot) :
      ResultRep catalog signatures functions mapping world prepared missing leaf cell projections (.inRight .word snapshot)
  | missing {source : Dynamic.Value} {reason : Dynamic.SemanticFault}
      (root : Dynamic.RootInitialValue cell (some source))
      (fault : Dynamic.ProjectionsFaults (some source) projections reason) :
      ResultRep catalog signatures functions mapping world prepared missing leaf cell projections
        (.inLeft prepared.optionalLeaf (.word (DataPlaceExactFault.token missing reason)))
  | uninitialized (root : Dynamic.RootInitialValue cell none) (nonempty : projections ≠ []) :
      ResultRep catalog signatures functions mapping world prepared missing leaf cell projections
        (.inLeft prepared.optionalLeaf (.word prepared.invalidProjection))

theorem ResultRep.extend {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel catalog} {mapping futureMapping : LocationMap} {world futureWorld : StoreTyping}
    {prepared : Prepared} {missing : TypeSystem.Ty → Word} {leaf : TypeSystem.Ty} {cell : Dynamic.Cell}
    {projections : List Dynamic.EvaluatedProjection} {value : Value}
    (related : ResultRep catalog signatures functions mapping world prepared missing leaf cell projections value)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    ResultRep catalog signatures functions futureMapping futureWorld prepared missing leaf cell projections value := by
  cases related with
  | read root read related => exact .read root read (related.extend maps worlds)
  | missing root fault => exact .missing root fault
  | uninitialized root nonempty => exact .uninitialized root nonempty

private theorem initial_exists {catalog : SourceCoreDataCatalog.Catalog} {model : GenericHeap.PayloadModel catalog}
    {mapping : LocationMap} {world : StoreTyping} {cell : Dynamic.Cell} {optional : Value} {type : Ty}
    (related : GenericHeap.CellRepresents model mapping world cell optional type) :
    ∃ initial, Dynamic.RootInitialValue cell initial := by
  cases related with
  | initialized => exact ⟨_, .initialized⟩
  | @uninitialized sourceType _ projected =>
    by_cases mappingType : ∃ key value, sourceType = .mapping key value
    · obtain ⟨key, value, rfl⟩ := mappingType
      exact ⟨_, .emptyMapping key value⟩
    · exact ⟨none, .uninitialized mappingType⟩

private theorem empty_projections {checked : Checked} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel checked.catalog} {mapping : LocationMap} {world : StoreTyping}
    {keys : List Value} {root leaf : TypeSystem.Ty} {type leafType : Ty} {steps : List PreparedStep}
    {projections : List Dynamic.EvaluatedProjection} {count : Nat}
    (path : DataPayloadReadPaths.Path checked signatures functions mapping world keys root type steps projections leaf leafType count)
    (empty : steps = []) : projections = [] := by
  induction path with
  | nil => rfl
  | member => cases empty
  | index => cases empty
  | comptime _ ih => exact ih empty

/-- A compositional argument-evaluation law. The source outcome and all
recursive helper executions are constructed from static preparation and full
payloads. The live-root theorem below supplies the actual load itself. -/
theorem evaluates {checked : Checked} {signatures : ProgramSignatures} {source : TypedSource}
    {functions : GenericHeap.PayloadModel checked.catalog} {mapping : LocationMap} {world : StoreTyping}
    (functionTypes : FunctionRuntimeTypes functions) (layouts : CatalogLayouts checked.catalog)
    {identities : Dynamic.Value → Word → Prop}
    (observations : FunctionObservations checked.catalog signatures functions identities) (faithful : IdentityFaithful identities)
    {prepared : Prepared} {cell : Dynamic.Cell} {optional : Value} {leaf : TypeSystem.Ty}
    {steps : List Step} {projections : List PlaceProjection} {sourceTypes : List TypeSystem.Ty}
    (path : RawPath checked signatures source cell.type prepared.route.rootType steps projections leaf prepared.route.leafType sourceTypes)
    {fuel : Nat} {missing : TypeSystem.Ty → Word}
    (preparation : DataPlaceMappingPreparation.Steps checked fuel missing 0 steps prepared.steps prepared.keys)
    {sources : List Dynamic.Value} {values : List Value} {evaluated : List Dynamic.EvaluatedProjection} {coreTypes : List Ty}
    (shaped : DataPlaceKeyOrder.Values projections sources evaluated)
    (keysRelated : DataExpressionSequence.Values (payloadModel checked.catalog signatures functions)
      mapping world sourceTypes coreTypes sources values)
    (keyLength : prepared.keyTypes.length = values.length)
    (rootLayout : RootLayout checked.catalog prepared cell.type)
    (cellRep : GenericHeap.CellRepresents (payloadModel checked.catalog signatures functions) mapping world cell optional prepared.route.rootType)
    {environment : Environment} {before store : Store} {keyType : Ty} {argument : Expr}
    (argumentEvaluated : Evaluates environment before argument (.pair optional (packValues values)) store) :
    ∃ result finalStore administrative,
      ResultRep checked.catalog signatures functions mapping world prepared missing leaf cell evaluated result ∧
      Evaluates environment before (.apply (getter prepared keyType) argument) result finalStore ∧
      finalStore = store ++ administrative := by
  obtain ⟨count, semanticPath⟩ := path.prepared_path preparation shaped keysRelated (allKeys := values)
    (by intro index value selected; simpa only [Nat.zero_add] using selected)
  obtain ⟨initial, root⟩ := initial_exists cellRep
  cases initial with
  | none =>
    by_cases empty : evaluated = []
    · subst evaluated
      obtain ⟨snapshot, finalStore, administrative, represented, ran, appended, _⟩ :=
        getter_evaluates observations faithful layouts prepared keyLength rootLayout cellRep root .nil semanticPath argumentEvaluated
      exact ⟨_, finalStore, administrative, .read root .nil represented, ran, appended⟩
    · obtain ⟨noMapping, optionalEq⟩ := root_absent rootLayout cellRep root
      have stepsNonempty : prepared.steps ≠ [] := fun impossible => empty (empty_projections semanticPath impossible)
      cases stepsEq : prepared.steps with
      | nil => exact (stepsNonempty stepsEq).elim
      | cons step rest =>
        refine ⟨_, store, [], .uninitialized root empty, .apply .lambda argumentEvaluated ?_, by simp⟩
        simp only [stepsEq, normalizeRoot, noMapping, LanguageResult.failure]
        rw [optionalEq]
        exact .caseLeft (.first (.var rfl)) (.inLeft .word)
  | some sourceRoot =>
    obtain ⟨coreRoot, normalized, rootRelated⟩ := root_present rootLayout cellRep root
    rcases DataPlaceReadTotality.read_or_fault functionTypes layouts path preparation shaped keysRelated rootRelated with
        ⟨selected, value, read, related⟩ | ⟨reason, fault⟩
    · obtain ⟨snapshot, finalStore, administrative, represented, ran, appended, _⟩ :=
        getter_evaluates observations faithful layouts prepared keyLength rootLayout cellRep root read semanticPath argumentEvaluated
      exact ⟨_, finalStore, administrative, .read root read represented, ran, appended⟩
    · have stepsNonempty : prepared.steps ≠ [] := by
        intro impossible
        have empty := empty_projections semanticPath impossible
        rw [empty] at fault
        cases fault
      obtain ⟨finalStore, administrative, ran, _, appended⟩ :=
        DataPlaceExactFault.preserves observations faithful layouts path preparation shaped keysRelated
          (allKeys := values) (by intro index value selected; simpa only [Nat.zero_add] using selected) keyLength
          rootRelated fault (coreRoot :: .pair optional (packValues values) :: environment) store
          (.var 0) (.second (.var 1)) .unit (.var rfl) (.second (.var rfl))
      refine ⟨_, finalStore, administrative, .missing root fault, .apply .lambda argumentEvaluated ?_, appended⟩
      cases stepsEq : prepared.steps with
      | nil => exact (stepsNonempty stepsEq).elim
      | cons step rest =>
        exact .caseRight (normalized.normalizes (.first (.var rfl)) store) (by simpa only [stepsEq] using ran)

/-- Every completed live-root getter yields an independently constructed source
snapshot or fault. The source heap is unchanged, while finite Core preservation
accounts for all appended helper cells and preserves the existing admin frame. -/
theorem reflects_at {checked : Checked} {signatures : ProgramSignatures} {source : TypedSource}
    {functions : GenericHeap.PayloadModel checked.catalog} {mapping : LocationMap} {world : StoreTyping}
    (functionTypes : FunctionRuntimeTypes functions) (layouts : CatalogLayouts checked.catalog)
    {identities : Dynamic.Value → Word → Prop}
    (observations : FunctionObservations checked.catalog signatures functions identities) (faithful : IdentityFaithful identities)
    {prepared : Prepared} {cell : Dynamic.Cell} {leaf : TypeSystem.Ty}
    {steps : List Step} {projections : List PlaceProjection} {sourceTypes : List TypeSystem.Ty}
    (path : RawPath checked signatures source cell.type prepared.route.rootType steps projections leaf prepared.route.leafType sourceTypes)
    {fuel : Nat} {missing : TypeSystem.Ty → Word}
    (preparation : DataPlaceMappingPreparation.Steps checked fuel missing 0 steps prepared.steps prepared.keys)
    {sources : List Dynamic.Value} {values : List Value} {evaluated : List Dynamic.EvaluatedProjection} {coreTypes : List Ty}
    (shaped : DataPlaceKeyOrder.Values projections sources evaluated)
    (keysRelated : DataExpressionSequence.Values (payloadModel checked.catalog signatures functions)
      mapping world sourceTypes coreTypes sources values)
    (keyLength : prepared.keyTypes.length = values.length)
    (rootLayout : RootLayout checked.catalog prepared cell.type)
    {heap : Dynamic.Heap} {store finalStore : Store} {sourceLocation : Dynamic.Location} {target : Location}
    (heaps : GenericHeap.HeapRepresents (payloadModel checked.catalog signatures functions) mapping world heap store)
    (reference : ReferenceRepresents mapping world sourceLocation target prepared.route.rootType)
    (read : Dynamic.Heap.Reads heap sourceLocation cell)
    {environment : Environment} {context : Core.Context} {keyType : Ty} {referenceExpression keyExpression : Expr} {result : Value}
    (environmentTyped : RuntimeEnvironmentHasTypes world environment context checked.catalog.definitions)
    (helperTyped : HasType context (.apply (getter prepared keyType) (.pair (.loadCell referenceExpression) keyExpression))
      (LanguageResult.resultType prepared.optionalLeaf) checked.catalog.definitions)
    (referenceSelected : Selects environment referenceExpression (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (keysSelected : Selects environment keyExpression (packValues values))
    (completed : Evaluates environment store (.apply (getter prepared keyType) (.pair (.loadCell referenceExpression) keyExpression))
      result finalStore) :
    ∃ futureWorld administrative,
      ResultRep checked.catalog signatures functions mapping futureWorld prepared missing leaf cell evaluated result ∧
      WorldExtends world futureWorld ∧
      GenericHeap.HeapRepresents (payloadModel checked.catalog signatures functions) mapping futureWorld heap finalStore ∧
      RuntimeValueHasType futureWorld result (LanguageResult.resultType prepared.optionalLeaf) checked.catalog.definitions ∧
      AdministrativePreserved mapping store mapping finalStore ∧ finalStore = store ++ administrative := by
  obtain ⟨optional, coreRead, cellRep⟩ := read_at heaps reference read
  have argument : Evaluates environment store (.pair (.loadCell referenceExpression) keyExpression)
      (.pair optional (packValues values)) store :=
    .pair (.loadCell (referenceSelected.evaluates store) coreRead) (keysSelected.evaluates store)
  obtain ⟨actual, after, administrative, represented, ran, appended⟩ :=
    evaluates functionTypes layouts observations faithful path preparation shaped keysRelated keyLength rootLayout cellRep argument
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed ran
  obtain ⟨futureWorld, extension, finalHeaps, typed, frame⟩ :=
    DataMappingHeap.evaluation_preserves_frame heaps environmentTyped helperTyped ran appended
  exact ⟨futureWorld, administrative, represented.extend (.refl _) extension, extension, finalHeaps, typed, frame, appended⟩

end Solcore.SourceSemantics.CoreLowering.DataPlaceGetterReflection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataPlaceSetterReflection
/-! The actual setter reloads the latest root, then reconstructs an independently
justified source update or structural fault. A computed replacement is carried
as a full payload. All helper evaluations are derived, and the actual source
cell remains unchanged until execute's later storeCell commits the result. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlaceSetterReflection
open Core Frontend Frontend.SourceInference GeneralHeap DataPatternValues DataPayload
open SourceCoreDataPlaces DataPlaceRouteCertificates DataPlaceSnapshot DataEquality

inductive ResultRep (catalog : SourceCoreDataCatalog.Catalog) (signatures : ProgramSignatures)
    (functions : GenericHeap.PayloadModel catalog) (mapping : LocationMap) (world : StoreTyping)
    (prepared : Prepared) (missing : TypeSystem.Ty → Word) (replacement : Dynamic.Value)
    (cell : Dynamic.Cell) (projections : List Dynamic.EvaluatedProjection) : Value → Prop where
  | updated {initial : Option Dynamic.Value} {source : Dynamic.Value} {value : Value}
      (root : Dynamic.RootInitialValue cell initial)
      (changed : Dynamic.ProjectionsUpdate (fun _ value => value = replacement) initial projections source)
      (related : ValueRep catalog signatures functions mapping world cell.type source value prepared.route.rootType) :
      ResultRep catalog signatures functions mapping world prepared missing replacement cell projections (.inRight .word value)
  | missing {source : Dynamic.Value} {reason : Dynamic.SemanticFault}
      (root : Dynamic.RootInitialValue cell (some source))
      (fault : Dynamic.ProjectionsFaults (some source) projections reason) :
      ResultRep catalog signatures functions mapping world prepared missing replacement cell projections
        (.inLeft prepared.route.rootType (.word (DataPlaceExactFault.token missing reason)))
  | uninitialized (root : Dynamic.RootInitialValue cell none) (nonempty : projections ≠ []) :
      ResultRep catalog signatures functions mapping world prepared missing replacement cell projections
        (.inLeft prepared.route.rootType (.word prepared.invalidProjection))

theorem ResultRep.extend {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel catalog} {mapping futureMapping : LocationMap} {world futureWorld : StoreTyping}
    {prepared : Prepared} {missing : TypeSystem.Ty → Word} {replacement : Dynamic.Value} {cell : Dynamic.Cell}
    {projections : List Dynamic.EvaluatedProjection} {value : Value}
    (related : ResultRep catalog signatures functions mapping world prepared missing replacement cell projections value)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    ResultRep catalog signatures functions futureMapping futureWorld prepared missing replacement cell projections value := by
  cases related with
  | updated root changed related => exact .updated root changed (related.extend maps worlds)
  | missing root fault => exact .missing root fault
  | uninitialized root nonempty => exact .uninitialized root nonempty

private theorem initial_exists {catalog : SourceCoreDataCatalog.Catalog} {model : GenericHeap.PayloadModel catalog}
    {mapping : LocationMap} {world : StoreTyping} {cell : Dynamic.Cell} {optional : Value} {type : Ty}
    (related : GenericHeap.CellRepresents model mapping world cell optional type) :
    ∃ initial, Dynamic.RootInitialValue cell initial := by
  cases related with
  | initialized => exact ⟨_, .initialized⟩
  | @uninitialized sourceType _ projected =>
    by_cases mappingType : ∃ key value, sourceType = .mapping key value
    · obtain ⟨key, value, rfl⟩ := mappingType
      exact ⟨_, .emptyMapping key value⟩
    · exact ⟨none, .uninitialized mappingType⟩

private theorem empty_projections {checked : Checked} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel checked.catalog} {mapping : LocationMap} {world : StoreTyping}
    {keys : List Value} {root leaf : TypeSystem.Ty} {type leafType : Ty} {steps : List PreparedStep}
    {projections : List Dynamic.EvaluatedProjection} {count : Nat}
    (path : DataPayloadReadPaths.Path checked signatures functions mapping world keys root type steps projections leaf leafType count)
    (empty : steps = []) : projections = [] := by
  induction path with
  | nil => rfl
  | member => cases empty
  | index => cases empty
  | comptime _ ih => exact ih empty

/-- Compositional finite setter evaluation. Source reconstruction is built
from the readable latest path, preserving first-match replacement and append
order. No source update or helper execution is an input premise. -/
theorem evaluates {checked : Checked} {signatures : ProgramSignatures} {source : TypedSource}
    {functions : GenericHeap.PayloadModel checked.catalog} {mapping : LocationMap} {world : StoreTyping}
    (functionTypes : FunctionRuntimeTypes functions) (layouts : CatalogLayouts checked.catalog)
    {identities : Dynamic.Value → Word → Prop}
    (observations : FunctionObservations checked.catalog signatures functions identities) (faithful : IdentityFaithful identities)
    {prepared : Prepared} {cell : Dynamic.Cell} {optional : Value} {leaf : TypeSystem.Ty}
    {steps : List Step} {projections : List PlaceProjection} {sourceTypes : List TypeSystem.Ty}
    (path : RawPath checked signatures source cell.type prepared.route.rootType steps projections leaf prepared.route.leafType sourceTypes)
    {fuel : Nat} {missing : TypeSystem.Ty → Word}
    (preparation : DataPlaceMappingPreparation.Steps checked fuel missing 0 steps prepared.steps prepared.keys)
    {sources : List Dynamic.Value} {values : List Value} {evaluated : List Dynamic.EvaluatedProjection} {coreTypes : List Ty}
    (shaped : DataPlaceKeyOrder.Values projections sources evaluated)
    (keysRelated : DataExpressionSequence.Values (payloadModel checked.catalog signatures functions)
      mapping world sourceTypes coreTypes sources values)
    (keyLength : prepared.keyTypes.length = values.length)
    (rootLayout : RootLayout checked.catalog prepared cell.type)
    (cellRep : GenericHeap.CellRepresents (payloadModel checked.catalog signatures functions) mapping world cell optional prepared.route.rootType)
    {replacementSource : Dynamic.Value} {replacement : Value}
    (replacementRep : ValueRep checked.catalog signatures functions mapping world leaf replacementSource replacement prepared.route.leafType)
    {environment : Environment} {before store : Store} {keyType : Ty} {argument : Expr}
    (argumentEvaluated : Evaluates environment before argument (.pair optional (.pair (packValues values) replacement)) store) :
    ∃ result finalStore administrative,
      ResultRep checked.catalog signatures functions mapping world prepared missing replacementSource cell evaluated result ∧
      Evaluates environment before (.apply (setter prepared keyType) argument) result finalStore ∧
      finalStore = store ++ administrative := by
  obtain ⟨count, semanticPath⟩ := path.prepared_path preparation shaped keysRelated (allKeys := values)
    (by intro index value selected; simpa only [Nat.zero_add] using selected)
  obtain ⟨initial, root⟩ := initial_exists cellRep
  cases initial with
  | none =>
    by_cases empty : evaluated = []
    · subst evaluated
      obtain ⟨value, finalStore, administrative, represented, ran, appended, _⟩ :=
        DataPlaceAssignmentWriteBack.setter_evaluates observations faithful layouts prepared keyLength rootLayout cellRep root
          (.leaf rfl) semanticPath replacementRep argumentEvaluated
      exact ⟨_, finalStore, administrative, .updated root (.leaf rfl) represented, ran, appended⟩
    · obtain ⟨noMapping, optionalEq⟩ := root_absent rootLayout cellRep root
      have stepsNonempty : prepared.steps ≠ [] := fun impossible => empty (empty_projections semanticPath impossible)
      cases stepsEq : prepared.steps with
      | nil => exact (stepsNonempty stepsEq).elim
      | cons step rest =>
        refine ⟨_, store, [], .uninitialized root empty, .apply .lambda argumentEvaluated ?_, by simp⟩
        simp only [stepsEq, normalizeRoot, noMapping, LanguageResult.failure]
        rw [optionalEq]
        exact .caseLeft (.first (.var rfl)) (.inLeft .word)
  | some sourceRoot =>
    obtain ⟨coreRoot, normalized, rootRelated⟩ := root_present rootLayout cellRep root
    rcases DataPlaceReadTotality.read_or_fault functionTypes layouts path preparation shaped keysRelated rootRelated with
        ⟨selected, value, read, related⟩ | ⟨reason, fault⟩
    · obtain ⟨updated, changed⟩ := DataPlaceUpdateTotality.read_update read replacementSource
      obtain ⟨value, finalStore, administrative, represented, ran, appended, _⟩ :=
        DataPlaceAssignmentWriteBack.setter_evaluates observations faithful layouts prepared keyLength rootLayout cellRep root
          changed semanticPath replacementRep argumentEvaluated
      exact ⟨_, finalStore, administrative, .updated root changed represented, ran, appended⟩
    · have stepsNonempty : prepared.steps ≠ [] := by
        intro impossible
        have empty := empty_projections semanticPath impossible
        rw [empty] at fault
        cases fault
      obtain ⟨finalStore, administrative, _, ran, appended⟩ :=
        DataPlaceExactFault.preserves observations faithful layouts path preparation shaped keysRelated
          (allKeys := values) (by intro index value selected; simpa only [Nat.zero_add] using selected) keyLength
          rootRelated fault (coreRoot :: .pair optional (.pair (packValues values) replacement) :: environment) store
          (.var 0) (.first (.second (.var 1))) (.second (.second (.var 1)))
          (.var rfl) (.first (.second (.var rfl)))
      refine ⟨_, finalStore, administrative, .missing root fault, .apply .lambda argumentEvaluated ?_, appended⟩
      cases stepsEq : prepared.steps with
      | nil => exact (stepsNonempty stepsEq).elim
      | cons step rest =>
        exact .caseRight (normalized.normalizes (.first (.var rfl)) store) (by simpa only [stepsEq] using ran)

/-- Reflect every completed setter on a live optional root. Reading the latest
cell is performed here; the source root update and helper-cell world extension
are outputs. The source write remains execute's separate following operation. -/
theorem reflects_at {checked : Checked} {signatures : ProgramSignatures} {source : TypedSource}
    {functions : GenericHeap.PayloadModel checked.catalog} {mapping : LocationMap} {world : StoreTyping}
    (functionTypes : FunctionRuntimeTypes functions) (layouts : CatalogLayouts checked.catalog)
    {identities : Dynamic.Value → Word → Prop}
    (observations : FunctionObservations checked.catalog signatures functions identities) (faithful : IdentityFaithful identities)
    {prepared : Prepared} {cell : Dynamic.Cell} {leaf : TypeSystem.Ty}
    {steps : List Step} {projections : List PlaceProjection} {sourceTypes : List TypeSystem.Ty}
    (path : RawPath checked signatures source cell.type prepared.route.rootType steps projections leaf prepared.route.leafType sourceTypes)
    {fuel : Nat} {missing : TypeSystem.Ty → Word}
    (preparation : DataPlaceMappingPreparation.Steps checked fuel missing 0 steps prepared.steps prepared.keys)
    {sources : List Dynamic.Value} {values : List Value} {evaluated : List Dynamic.EvaluatedProjection} {coreTypes : List Ty}
    (shaped : DataPlaceKeyOrder.Values projections sources evaluated)
    (keysRelated : DataExpressionSequence.Values (payloadModel checked.catalog signatures functions)
      mapping world sourceTypes coreTypes sources values)
    (keyLength : prepared.keyTypes.length = values.length)
    (rootLayout : RootLayout checked.catalog prepared cell.type)
    {replacementSource : Dynamic.Value} {replacement : Value}
    (replacementRep : ValueRep checked.catalog signatures functions mapping world leaf replacementSource replacement prepared.route.leafType)
    {heap : Dynamic.Heap} {store finalStore : Store} {sourceLocation : Dynamic.Location} {target : Location}
    (heaps : GenericHeap.HeapRepresents (payloadModel checked.catalog signatures functions) mapping world heap store)
    (reference : ReferenceRepresents mapping world sourceLocation target prepared.route.rootType)
    (read : Dynamic.Heap.Reads heap sourceLocation cell)
    {environment : Environment} {context : Core.Context} {keyType : Ty} {referenceExpression keyExpression replacementExpression : Expr} {result : Value}
    (environmentTyped : RuntimeEnvironmentHasTypes world environment context checked.catalog.definitions)
    (helperTyped : HasType context (.apply (setter prepared keyType)
        (.pair (.loadCell referenceExpression) (.pair keyExpression replacementExpression)))
      (LanguageResult.resultType prepared.route.rootType) checked.catalog.definitions)
    (referenceSelected : Selects environment referenceExpression (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (keysSelected : Selects environment keyExpression (packValues values))
    (replacementSelected : Selects environment replacementExpression replacement)
    (completed : Evaluates environment store (.apply (setter prepared keyType)
      (.pair (.loadCell referenceExpression) (.pair keyExpression replacementExpression))) result finalStore) :
    ∃ futureWorld administrative,
      ResultRep checked.catalog signatures functions mapping futureWorld prepared missing replacementSource cell evaluated result ∧
      WorldExtends world futureWorld ∧
      GenericHeap.HeapRepresents (payloadModel checked.catalog signatures functions) mapping futureWorld heap finalStore ∧
      RuntimeValueHasType futureWorld result (LanguageResult.resultType prepared.route.rootType) checked.catalog.definitions ∧
      AdministrativePreserved mapping store mapping finalStore ∧ finalStore = store ++ administrative := by
  obtain ⟨optional, coreRead, cellRep⟩ := read_at heaps reference read
  have argument : Evaluates environment store (.pair (.loadCell referenceExpression) (.pair keyExpression replacementExpression))
      (.pair optional (.pair (packValues values) replacement)) store :=
    .pair (.loadCell (referenceSelected.evaluates store) coreRead)
      (.pair (keysSelected.evaluates store) (replacementSelected.evaluates store))
  obtain ⟨actual, after, administrative, represented, ran, appended⟩ :=
    evaluates functionTypes layouts observations faithful path preparation shaped keysRelated keyLength rootLayout cellRep replacementRep argument
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed ran
  obtain ⟨futureWorld, extension, finalHeaps, typed, frame⟩ :=
    DataMappingHeap.evaluation_preserves_frame heaps environmentTyped helperTyped ran appended
  exact ⟨futureWorld, administrative, represented.extend (.refl _) extension, extension, finalHeaps, typed, frame, appended⟩

end Solcore.SourceSemantics.CoreLowering.DataPlaceSetterReflection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataPlaceModifierReflection
/-! Completed place modifiers reflect the independently specified source leaf
operation. Plain assignment accepts every full payload; compound Word/Integer
operations are total when initialized. Absence is the only remaining failure,
and is retained for the enclosing latest-root ordering proof. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlaceModifierReflection
open Core Frontend Frontend.SourceInference GeneralHeap DataPayload DataEquality
open SourceCoreDataPlaces

inductive ResultRep (catalog : SourceCoreDataCatalog.Catalog) (signatures : ProgramSignatures)
    (functions : GenericHeap.PayloadModel catalog) (mapping : LocationMap) (world : StoreTyping)
    (sourceType : TypeSystem.Ty) (type : Ty) (operator : Syntax.ValueAssignOp)
    (snapshot : Option Dynamic.Value) (right : Dynamic.Value) (invalid : Word) : Value → Prop where
  | applied {source : Dynamic.Value} {value : Value}
      (applied : Dynamic.AssignmentValueApplies operator snapshot right source)
      (related : ValueRep catalog signatures functions mapping world sourceType source value type) :
      ResultRep catalog signatures functions mapping world sourceType type operator snapshot right invalid (.inRight .word value)
  | uninitialized (absent : snapshot = none) (notEqual : operator ≠ .equal) :
      ResultRep catalog signatures functions mapping world sourceType type operator snapshot right invalid (.inLeft type (.word invalid))
  /-- Core's total modifier gives a leaf that `guard` later rejects, because
  the source panics on these operands once the latest root is traversed. -/
  | panicking {changed : Dynamic.Value} {value : Value} {operation : BinaryOp}
      (zero : right = .word Word.zero)
      (selected : binaryOperator (type = .integer) operator = some ⟨operation, true⟩)
      (panics : Dynamic.AssignmentOperandsPanic operator snapshot right SourceCorePanics.divisionByZero)
      (related : ValueRep catalog signatures functions mapping world sourceType changed value type) :
      ResultRep catalog signatures functions mapping world sourceType type operator snapshot right invalid (.inRight .word value)

/-- Total source/Core leaf behavior derived from payloads and the actual
operator spelling. Invalid operands are not conflated with machine faults. -/
theorem evaluates {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel catalog} {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {type : Ty} {snapshot : Option Dynamic.Value}
    {right : Dynamic.Value} {snapshotCore rightCore : Value} {operator : Syntax.ValueAssignOp}
    (profile : operator = .equal ∨ sourceType = .word ∨ sourceType = .integer ∧ operator.wordOnly = false)
    (snapshotRep : DataPlaceSnapshot.OptionalRep catalog signatures functions mapping world sourceType type snapshot snapshotCore)
    (rightRep : ValueRep catalog signatures functions mapping world sourceType right rightCore type)
    {environment : Environment} {snapshotExpression rightExpression : Expr}
    (snapshotSelected : Selects environment snapshotExpression snapshotCore)
    (rightSelected : Selects environment rightExpression rightCore) (store : Store) (invalid : Word) :
    ∃ result, ResultRep catalog signatures functions mapping world sourceType type operator snapshot right invalid result ∧
      Evaluates environment store
        (modified type (binaryOperator (type = .integer) operator) false snapshotExpression rightExpression invalid) result store := by
  by_cases equal : operator = .equal
  · subst operator
    exact ⟨_, .applied (.equal _ _) rightRep, DataPlaceModifier.equal_modified rightSelected store invalid⟩
  · cases snapshotRep with
    | absent =>
      refine ⟨_, .uninitialized rfl equal, ?_⟩
      cases operator <;> try exact (equal rfl).elim
      all_goals exact .caseLeft (snapshotSelected.evaluates store) (.inLeft .word)
    | present related =>
      by_cases zero : operator.mayPanic = true ∧ right = .word Word.zero
      · obtain ⟨panics, rfl⟩ := zero
        have word := DataPlaceModifier.panicking_word profile panics
        subst word
        cases rightRep with
        | word _ =>
          obtain ⟨changed, value, operation, changedRep, selected, panicked, ran, _⟩ :=
            DataPlaceModifier.initialized_panic panics related snapshotSelected rightSelected store invalid
          exact ⟨_, .panicking rfl selected panicked changedRep, ran⟩
      · have divisor : operator.mayPanic = false ∨ right ≠ .word Word.zero := by
          by_cases panics : operator.mayPanic = true
          · exact .inr fun same => zero ⟨panics, same⟩
          · exact .inl (by simpa using panics)
        obtain ⟨source, value, resultRep, sourceApplied, ran, _⟩ :=
          DataPlaceModifier.initialized_success (profile.resolve_left equal) divisor related rightRep
            snapshotSelected rightSelected store invalid
        exact ⟨_, .applied sourceApplied resultRep, ran⟩

theorem reflects {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel catalog} {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {type : Ty} {snapshot : Option Dynamic.Value}
    {right : Dynamic.Value} {snapshotCore rightCore : Value} {operator : Syntax.ValueAssignOp}
    (profile : operator = .equal ∨ sourceType = .word ∨ sourceType = .integer ∧ operator.wordOnly = false)
    (snapshotRep : DataPlaceSnapshot.OptionalRep catalog signatures functions mapping world sourceType type snapshot snapshotCore)
    (rightRep : ValueRep catalog signatures functions mapping world sourceType right rightCore type)
    {environment : Environment} {snapshotExpression rightExpression : Expr}
    (snapshotSelected : Selects environment snapshotExpression snapshotCore)
    (rightSelected : Selects environment rightExpression rightCore)
    {store after : Store} {invalid : Word} {result : Value}
    (completed : Evaluates environment store
      (modified type (binaryOperator (type = .integer) operator) false snapshotExpression rightExpression invalid) result after) :
    after = store ∧ ResultRep catalog signatures functions mapping world sourceType type operator snapshot right invalid result := by
  obtain ⟨actual, represented, ran⟩ := evaluates profile snapshotRep rightRep snapshotSelected rightSelected store invalid
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed ran
  exact ⟨rfl, represented⟩

/-- The absent branch gives the source operand fault, but the enclosing
assignment still must show the latest structural path was traversable first. -/
theorem ResultRep.invalid {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel catalog} {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {type : Ty} {snapshot : Option Dynamic.Value} {right : Dynamic.Value}
    {operator : Syntax.ValueAssignOp} {invalid token : Word}
    (related : ResultRep catalog signatures functions mapping world sourceType type operator snapshot right invalid (.inLeft type (.word token))) :
    token = invalid ∧ snapshot = none ∧ Dynamic.AssignmentOperandsInvalid operator snapshot right := by
  cases related with
  | uninitialized absent notEqual => exact ⟨rfl, absent, absent ▸ .uninitialized notEqual⟩

end Solcore.SourceSemantics.CoreLowering.DataPlaceModifierReflection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataPlaceCommitReflection
/-! Reflect execute's final mapped write. The source write is constructed from
the live source cell and the authenticated reconstructed root. No source write
or continuation execution is assumed. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlaceCommitReflection
open Core Frontend Frontend.SourceInference GeneralHeap DataPayload DataEquality

/-- Existing source locations can be updated without changing their declaration
metadata or any other source cell. -/
theorem source_writes {heap : Dynamic.Heap} {location : Dynamic.Location} {cell : Dynamic.Cell}
    (read : Dynamic.Heap.Reads heap location cell) (value : Dynamic.Value) :
    Dynamic.Heap.Writes heap location (some value)
      ⟨heap.cells.set location.index {cell with value := some value}⟩ := by
  have replace : ∀ {cells : List Dynamic.Cell} {index : Nat} {old : Dynamic.Cell},
      Dynamic.Heap.CellAt cells index old →
      Dynamic.Heap.CellsWrite cells index {old with value := some value}
        (cells.set index {old with value := some value}) := by
    intro cells index old selected
    induction selected with
    | head => exact .head
    | tail selected ih => exact .tail ih
  cases read with
  | intro selected => exact .intro (.intro selected) (replace selected)

/-- A constant leaf replacement can be reinterpreted as any independently
proved source modifier producing that value. Traversal and insertion order are
preserved, including duplicate mapping keys. -/
theorem update_of_replacement {Modify : Option Dynamic.Value → Dynamic.Value → Prop}
    {replacement updated : Dynamic.Value} {initial : Option Dynamic.Value}
    {projections : List Dynamic.EvaluatedProjection}
    (changed : Dynamic.ProjectionsUpdate (fun _ value => value = replacement) initial projections updated)
    (modified : ∀ snapshot, Modify snapshot replacement) :
    Dynamic.ProjectionsUpdate Modify initial projections updated := by
  induction changed with
  | leaf same => exact .leaf (same ▸ modified _)
  | indexFound found _ inserted ih => exact .indexFound found ih inserted
  | indexDefault absent defaulted _ inserted ih => exact .indexDefault absent defaulted ih inserted
  | member selected _ replaced ih => exact .member selected ih replaced

/-- Any completed actual storeCell commits precisely the reconstructed source
root once. The mapped heap and old administrative cells are preserved at the
same world; helper allocations have already been reflected before this step. -/
theorem reflects_storeCell {catalog : SourceCoreDataCatalog.Catalog} {model : GenericHeap.PayloadModel catalog}
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store finalStore : Store}
    {location : Dynamic.Location} {target : Location} {cell : Dynamic.Cell} {type : Ty}
    {sourceValue : Dynamic.Value} {value result : Value}
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (reference : ReferenceRepresents mapping world location target type)
    (read : Dynamic.Heap.Reads heap location cell)
    (represented : model.Represents mapping world cell.type sourceValue value type)
    {environment : Environment} {referenceExpression valueExpression : Expr}
    (referenceSelected : Selects environment referenceExpression (.cellRef (OptionalCell.cellType type) target))
    (valueSelected : Selects environment valueExpression value)
    (completed : Evaluates environment store
      (.storeCell referenceExpression (.inRight .unit valueExpression)) result finalStore) :
    ∃ after, result = .unit ∧ Dynamic.Heap.Writes heap location (some sourceValue) after ∧
      GenericHeap.HeapRepresents model mapping world after finalStore ∧
      AdministrativePreserved mapping store mapping finalStore ∧
      Dynamic.HeapMetadataExtend heap after ∧
      finalStore.read? target = some (.inRight .unit value) := by
  have written := source_writes read sourceValue
  obtain ⟨updated, coreWritten, finalHeaps, frame⟩ := heaps.write_initialized reference read represented written
  obtain ⟨_, optional, _, _, _, coreRead, _⟩ := heaps.cells reference.mapped
  have actual : Evaluates environment store
      (.storeCell referenceExpression (.inRight .unit valueExpression)) .unit updated :=
    .storeCell (referenceSelected.evaluates store) coreRead (.inRight (valueSelected.evaluates store)) coreWritten
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed actual
  exact ⟨_, rfl, written, finalHeaps, frame, .of_write written, Store.write?_reads_written coreWritten⟩

end Solcore.SourceSemantics.CoreLowering.DataPlaceCommitReflection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataPlaceAssignmentPrefix
/-! Whole emitted assignment faults before modification. The target keys and
snapshot getter are reconstructed from independent source resolution, and the
RHS is obtained from the universal child theorem under the real three slots.
-/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlaceAssignmentPrefix
open Core Frontend Frontend.SourceInference GeneralHeap DataPatternValues DataPayload
open GenericExpressionMeaning SourceCoreDataPlaces DataPlaceExecution

theorem rhs_fault {checked : SourceCoreDataCatalog.Checked} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel checked.catalog} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty}
    {administrativeContext : Core.Context}
    (layout : DataPlaceResolvedTarget.Layout checked signatures functions source certificate scope place prepared codes sourceTypes
      (SourceCoreLocalCell.coreContext scope ++ administrativeContext))
    (meaning : Preserves (payloadModel checked.catalog signatures functions) program context evidence source certificate faults)
    {identities : Dynamic.Value → Word → Prop}
    (observations : FunctionObservations checked.catalog signatures functions identities)
    (faithful : DataEquality.IdentityFaithful identities) (layouts : CatalogLayouts checked.catalog)
    {rhs : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (rhsGenerated : certificate scope rhs lowered) (found : source.lookupExpression? rhs = some node)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {coreEnvironment : Environment}
    {before targetHeap after : Dynamic.Heap} {store : Store} {sourceTarget : Dynamic.ResolvedPlace} {index : Nat}
    (environments : DataHeap.EnvRepresents checked.catalog mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GenericHeap.HeapRepresents (payloadModel checked.catalog signatures functions) mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootType : sourceTarget.rootType = prepared.route.rootSourceType)
    (resolve : Dynamic.SourcePlaceResolves program context evidence source environment before place sourceTarget targetHeap)
    {reason : Dynamic.SemanticFault}
    (failed : Dynamic.ExpressionFaults program context evidence source environment targetHeap rhs reason after)
    (operator : Syntax.ValueAssignOp) (next : Expr) (outputType : Ty) (invalidOperand : Word) :
    ∃ token finalStore finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator rhs reason after ∧
      Evaluates coreEnvironment store
        (execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalidOperand)
        (.inLeft outputType (.word token)) finalStore ∧
      faults reason token ∧
      GenericHeap.HeapRepresents (payloadModel checked.catalog signatures functions) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨target, coreLookup⟩ := DataPlaceResolvedTarget.preserves layout meaning observations faithful layouts
    environments heaps locals slot rootType resolve
  have sameEnvironment : ReadOnly.EnvironmentsAgree Renaming.id coreEnvironment coreEnvironment := by
    intro i v selected; exact selected
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    DataPlaceChildExpressions.preserves meaning rhsGenerated found
      (environments.extend target.maps target.worlds) target.heaps (locals.mono target.metadata) sameEnvironment
      [target.snapshot, packValues target.values, .cellRef (OptionalCell.cellType prepared.route.rootType) target.target]
      (.fault failed)
  cases represented with
  | @fault _ token reasonRep =>
    have rhsEvaluated : Evaluates
        (snapshotEnvironment prepared.route.rootType target.target (packValues target.values) target.snapshot coreEnvironment)
        target.store (shift 3 lowered.expression) (.inLeft lowered.type (.word token)) finalStore := by
      simpa only [Expr.rename_id, List.length_cons, List.length_nil, List.cons_append, List.nil_append,
        snapshotEnvironment, keysEnvironment, referenceEnvironment] using evaluated
    exact ⟨token, finalStore, finalMap, finalWorld, .rhs resolve failed,
      execute_rhs_failure (.var coreLookup) target.keysEvaluated target.snapshotEvaluated rhsEvaluated,
      reasonRep, finalHeaps, target.maps.trans maps, target.worlds.trans worlds,
      target.frame.trans frame, target.metadata.trans metadata⟩

end Solcore.SourceSemantics.CoreLowering.DataPlaceAssignmentPrefix
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataPlacePrefixReflection
/-! Reflection of execute's real reference/key/getter prefix. The universal
child theorem reconstructs each index trace in source order, before the live
root is read. Success exposes the real three-slot RHS continuation; failures
return the source fault and skip every later phase. These executions are output
witnesses, not fields of a static compiler certificate. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlacePrefixReflection
open Core Frontend Frontend.SourceInference GeneralHeap DataPatternValues DataPayload
open GenericExpressionMeaning SourceCoreDataPlaces DataPlaceExecution

/-- The literal remaining subtree of `execute`, after its snapshot binder. -/
def remainder (prepared : Prepared) (keyType : Ty) (rhs next : Expr) (outputType : Ty)
    (operator : Option Frontend.SourceCoreDataPlaces.Modifier) (bitNot : Bool) (invalid : Word) : Expr :=
  LanguageResult.bind outputType (shift 3 rhs)
    (LanguageResult.bind outputType
      (modified prepared.route.leafType operator bitNot (.var 1) (.var 0) invalid)
      (LanguageResult.bind outputType
        (.apply (setter prepared keyType) (.pair (.loadCell (.var 4)) (.pair (.var 3) (.var 0))))
        (guard outputType operator (.letE (.storeCell (.var 5) (.inRight .unit (.var 0))) (shift 7 next)))))

theorem execute_eq (prepared : Prepared) (reference : Expr) (keys : SourceCoreBasic.LoweredExpr)
    (rhs next : Expr) (outputType : Ty) (operator : Option Frontend.SourceCoreDataPlaces.Modifier) (bitNot : Bool) (invalid : Word) :
    execute prepared reference keys rhs next outputType operator bitNot invalid =
      .letE reference (LanguageResult.bind outputType (shift 1 keys.expression)
        (LanguageResult.bind outputType (.apply (getter prepared keys.type) (.pair (.loadCell (.var 1)) (.var 0)))
          (remainder prepared keys.type rhs next outputType operator bitNot invalid))) := rfl

private theorem missing_token {faults : FaultRep} {missing : TypeSystem.Ty → Word}
    (tokens : ∀ type, faults (.missingMappingDefault type) (missing type))
    {initial : Option Dynamic.Value} {projections : List Dynamic.EvaluatedProjection} {reason : Dynamic.SemanticFault}
    (fault : Dynamic.ProjectionsFaults initial projections reason) : faults reason (DataPlaceExactFault.token missing reason) := by
  induction fault with
  | indexDefaultUnavailable => exact tokens _
  | indexFound _ _ _ ih | indexDefault _ _ _ _ ih | member _ _ ih => exact ih

/-- A semantic prefix result. The success case retains every actual value and
store needed by RHS/modifier/setter reflection, including the source snapshot.
The failure case retains the final child/getter heap and diagnostic relation. -/
inductive Result (checked : SourceCoreDataCatalog.Checked) (signatures : ProgramSignatures)
    (functions : GenericHeap.PayloadModel checked.catalog) (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (faults : FaultRep)
    (prepared : Prepared) (codes : List SourceCoreBasic.LoweredExpr) (sourceTypes : List TypeSystem.Ty)
    (place : PlaceResolution) (environment : Dynamic.Environment) (coreEnvironment : Environment)
    (before : Dynamic.Heap) (store : Store) (mapping : LocationMap) (world : StoreTyping)
    (rhs next : Expr) (outputType : Ty) (operator : Option Frontend.SourceCoreDataPlaces.Modifier) (bitNot : Bool) (invalid : Word)
    (result : Value) (finalStore : Store) : Prop where
  | fault {reason : Dynamic.SemanticFault} {token : Word} {after : Dynamic.Heap}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      (sourceFault : Dynamic.SourcePlaceFaults program context evidence source environment before place reason after)
      (resultEq : result = .inLeft outputType (.word token)) (tokenRep : faults reason token)
      (heaps : GenericHeap.HeapRepresents (payloadModel checked.catalog signatures functions) finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after) :
      Result checked signatures functions program context evidence source faults prepared codes sourceTypes place
        environment coreEnvironment before store mapping world rhs next outputType operator bitNot invalid result finalStore
  | resolved {target : Dynamic.ResolvedPlace} {after : Dynamic.Heap}
      (sourceTrace : Dynamic.SourcePlaceResolves program context evidence source environment before place target after)
      (execution : DataPlaceResolvedTarget.Execution checked signatures functions prepared codes sourceTypes place target
        coreEnvironment store mapping world before after)
      (continuation : Evaluates (snapshotEnvironment prepared.route.rootType execution.target (packValues execution.values)
        execution.snapshot coreEnvironment) execution.store
        (remainder prepared (SourceCoreCalls.packArguments codes).type rhs next outputType operator bitNot invalid) result finalStore) :
      Result checked signatures functions program context evidence source faults prepared codes sourceTypes place
        environment coreEnvironment before store mapping world rhs next outputType operator bitNot invalid result finalStore

/-- Every actual completed assignment first either produces a source target
fault or resolves a source target before entering its RHS. No source index
trace or child/helper execution is supplied by the caller. -/
theorem reflects {checked : SourceCoreDataCatalog.Checked} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel checked.catalog} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {administrativeContext : Core.Context}
    (layout : DataPlaceResolvedTarget.Layout checked signatures functions source certificate scope place prepared codes sourceTypes
      (SourceCoreLocalCell.coreContext scope ++ administrativeContext))
    {steps : List Step} {fuel : Nat} {missing : TypeSystem.Ty → Word}
    (raw : DataPlaceRouteCertificates.RawPath checked signatures source prepared.route.rootSourceType prepared.route.rootType
      steps place.projections place.type prepared.route.leafType sourceTypes)
    (preparation : DataPlaceMappingPreparation.Steps checked fuel missing 0 steps prepared.steps prepared.keys)
    (meaning : Reflects (payloadModel checked.catalog signatures functions) program context evidence source certificate faults)
    (functionTypes : FunctionRuntimeTypes functions) (layouts : CatalogLayouts checked.catalog)
    {identities : Dynamic.Value → Word → Prop}
    (observations : FunctionObservations checked.catalog signatures functions identities) (faithful : DataEquality.IdentityFaithful identities)
    (missingTokens : ∀ type, faults (.missingMappingDefault type) (missing type))
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {coreEnvironment : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {sourceLocation : Dynamic.Location} {initialCell : Dynamic.Cell} {index : Nat}
    (environments : DataHeap.EnvRepresents checked.catalog mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GenericHeap.HeapRepresents (payloadModel checked.catalog signatures functions) mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (lookup : Dynamic.Environment.LooksUp environment place.root sourceLocation)
    (initialRead : Dynamic.Heap.Reads before sourceLocation initialCell)
    (rootType : initialCell.type = prepared.route.rootSourceType)
    [FunctionCalls.FaultTokens faults] (invalidToken : faults (.uninitializedLocation sourceLocation) prepared.invalidProjection)
    {rhs next : Expr} {outputType : Ty} {operator : Option Frontend.SourceCoreDataPlaces.Modifier} {bitNot : Bool} {invalid : Word} {result : Value}
    (completed : Evaluates coreEnvironment store
      (execute prepared (.var index) (SourceCoreCalls.packArguments codes) rhs next outputType operator bitNot invalid)
      result finalStore) :
    Result checked signatures functions program context evidence source faults prepared codes sourceTypes place environment
      coreEnvironment before store mapping world rhs next outputType operator bitNot invalid result finalStore := by
  obtain ⟨target, coreLookup, reference⟩ := environments.lookup_visible lookup slot
  have sameEnvironment : ReadOnly.EnvironmentsAgree Renaming.id coreEnvironment coreEnvironment := by
    intro i value found; exact found
  have reflectKeys := fun {keyValue : Value} {keyStore : Store}
      (evaluated : Evaluates (referenceEnvironment prepared.route.rootType target coreEnvironment) store
        (shift 1 (SourceCoreCalls.packArguments codes).expression) keyValue keyStore) =>
    DataPlaceKeyOrder.reflects layout.keys meaning environments heaps locals
      (DataPlaceChildExpressions.prefix_agrees sameEnvironment
        [.cellRef (OptionalCell.cellType prepared.route.rootType) target])
      (by simpa only [DataPlaceChildExpressions.rename_prefix, Expr.rename_id, List.length_cons, List.length_nil,
        List.cons_append, List.nil_append, referenceEnvironment] using evaluated)
  cases completed with
  | letE referenceEvaluated tail =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic referenceEvaluated (Evaluates.var coreLookup)
    cases tail with
    | caseLeft keysEvaluated failed =>
      obtain ⟨outcome, after, finalMap, finalWorld, sourceTrace, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
        reflectKeys keysEvaluated
      cases represented with
      | fault tokenRep =>
        cases sourceTrace with
        | fault sourceTrace =>
          cases failed with
          | inLeft valueEvaluated =>
            cases valueEvaluated with
            | var found =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at found
              subst_vars
              exact .fault (.projectionExpression lookup initialRead sourceTrace) rfl tokenRep finalHeaps maps worlds frame metadata
    | caseRight keysEvaluated tail =>
      obtain ⟨outcome, keyHeap, keyMap, keyWorld, sourceTrace, represented, keyHeaps, keyMaps, keyWorlds, keyFrame, metadata⟩ :=
        reflectKeys keysEvaluated
      cases represented with
      | @values sources values keysRelated =>
        cases sourceTrace with
        | @values _ evaluated _ shaped sourceTrace =>
          obtain ⟨currentCell, currentRead, currentType, _⟩ := metadata sourceLocation initialCell initialRead
          have currentReference := reference.extend keyMaps keyWorlds
          have typedEnvironment : RuntimeEnvironmentHasTypes keyWorld
              (keysEnvironment prepared.route.rootType target (packValues values) coreEnvironment)
              ((SourceCoreCalls.packArguments codes).type :: OptionalCell.referenceType prepared.route.rootType ::
                (SourceCoreLocalCell.coreContext scope ++ administrativeContext)) checked.catalog.definitions :=
            .cons (DataPlaceResolvedTarget.values_typed keysRelated)
              (.cons (.cellRef currentReference.typed) ((environments.extend keyMaps keyWorlds).runtime_hasTypes))
          have currentRaw : DataPlaceRouteCertificates.RawPath checked signatures source currentCell.type prepared.route.rootType
              steps place.projections place.type prepared.route.leafType sourceTypes := by
            rw [currentType, rootType]; exact raw
          have currentLayout : DataPlaceSnapshot.RootLayout checked.catalog prepared currentCell.type := by
            rw [currentType, rootType]; exact layout.root
          have keyLength : prepared.keyTypes.length = values.length := layout.keyTypes ▸ keysRelated.length.2
          have reflectGetter := fun {snapshotValue : Value} {snapshotStore : Store}
              (evaluated : Evaluates (keysEnvironment prepared.route.rootType target (packValues values) coreEnvironment) _
                (.apply (getter prepared (SourceCoreCalls.packArguments codes).type) (.pair (.loadCell (.var 1)) (.var 0)))
                snapshotValue snapshotStore) =>
            DataPlaceGetterReflection.reflects_at functionTypes layouts observations faithful currentRaw preparation
              shaped keysRelated keyLength currentLayout keyHeaps currentReference currentRead typedEnvironment layout.getterTyped
              (.var rfl) (.var rfl) evaluated
          cases tail with
          | caseLeft getterEvaluated failed =>
            obtain ⟨futureWorld, administrative, resultRep, extension, finalHeaps, _, frame, _⟩ := reflectGetter getterEvaluated
            cases resultRep with
            | missing root fault =>
              cases failed with
              | inLeft valueEvaluated =>
                cases valueEvaluated with
                | var found =>
                  simp only [List.getElem?_cons_zero, Option.some.injEq] at found
                  subst_vars
                  exact .fault (.projectionRead lookup initialRead sourceTrace currentRead root fault) rfl
                    (missing_token missingTokens fault) finalHeaps keyMaps (keyWorlds.trans extension) (keyFrame.trans frame) metadata
            | uninitialized root nonempty =>
              cases root with
              | uninitialized notMapping =>
                cases failed with
                | inLeft valueEvaluated =>
                  cases valueEvaluated with
                  | var found =>
                    simp only [List.getElem?_cons_zero, Option.some.injEq] at found
                    subst_vars
                    exact .fault (.uninitialized lookup initialRead sourceTrace currentRead rfl notMapping nonempty) rfl
                      invalidToken finalHeaps keyMaps (keyWorlds.trans extension) (keyFrame.trans frame) metadata
          | caseRight getterEvaluated remaining =>
            obtain ⟨futureWorld, administrative, resultRep, extension, finalHeaps, _, frame, _⟩ := reflectGetter getterEvaluated
            cases resultRep with
            | @read initial selected snapshot root read snapshotRelated =>
              exact .resolved (.intro lookup initialRead sourceTrace currentRead root read)
                { target := target
                  sources := sources
                  values := values
                  snapshot := _
                  keyStore := _
                  store := _
                  mapping := keyMap
                  world := futureWorld
                  reference := currentReference.extend (.refl _) extension
                  shaped := shaped
                  keysEvaluated := keysEvaluated
                  snapshotEvaluated := getterEvaluated
                  keysRelated := keysRelated.extend (.refl _) extension
                  snapshotRelated := snapshotRelated
                  heaps := finalHeaps
                  maps := keyMaps
                  worlds := keyWorlds.trans extension
                  frame := keyFrame.trans frame
                  metadata := metadata }
                remaining

end Solcore.SourceSemantics.CoreLowering.DataPlacePrefixReflection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataPlaceRhsReflection
/-! The actual three-slot RHS continuation reflects through the universal child
expression theorem. It either constructs the source RHS fault with its effects,
or retains the RHS value/heap and the actual four-slot modifier continuation.
Prefix/RHS executions are semantic output witnesses, never static assumptions. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlaceRhsReflection
open Core Frontend Frontend.SourceInference GeneralHeap DataPatternValues DataPayload
open GenericExpressionMeaning SourceCoreDataPlaces DataPlaceExecution

/-- The literal subtree of execute after binding its RHS value. -/
def remainder (prepared : Prepared) (keyType : Ty) (next : Expr) (outputType : Ty)
    (operator : Option Frontend.SourceCoreDataPlaces.Modifier) (invalid : Word) : Expr :=
  LanguageResult.bind outputType
    (modified prepared.route.leafType operator false (.var 1) (.var 0) invalid)
    (LanguageResult.bind outputType
      (.apply (setter prepared keyType) (.pair (.loadCell (.var 4)) (.pair (.var 3) (.var 0))))
      (guard outputType operator (.letE (.storeCell (.var 5) (.inRight .unit (.var 0))) (shift 7 next))))

theorem prefix_remainder_eq (prepared : Prepared) (keyType : Ty) (rhs next : Expr)
    (outputType : Ty) (operator : Option Frontend.SourceCoreDataPlaces.Modifier) (invalid : Word) :
    DataPlacePrefixReflection.remainder prepared keyType rhs next outputType operator false invalid =
      LanguageResult.bind outputType (shift 3 rhs) (remainder prepared keyType next outputType operator invalid) := rfl

/-- Actual RHS output, including independent source meaning and all heap,
world and admin-frame extensions relative to the already reflected snapshot. -/
structure Execution (checked : SourceCoreDataCatalog.Checked) (signatures : ProgramSignatures)
    (functions : GenericHeap.PayloadModel checked.catalog) (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment)
    (prepared : Prepared) (codes : List SourceCoreBasic.LoweredExpr) (sourceTypes : List TypeSystem.Ty)
    (place : PlaceResolution) (target : Dynamic.ResolvedPlace) (coreEnvironment : Environment)
    (initialStore : Store) (initialMap : LocationMap) (initialWorld : StoreTyping) (before targetHeap : Dynamic.Heap)
    (resolution : DataPlaceResolvedTarget.Execution checked signatures functions prepared codes sourceTypes place target
      coreEnvironment initialStore initialMap initialWorld before targetHeap)
    (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr) where
  right : Dynamic.Value
  value : Value
  heap : Dynamic.Heap
  store : Store
  mapping : LocationMap
  world : StoreTyping
  sourceTrace : Dynamic.ExpressionEvaluates program context evidence source environment targetHeap id right heap
  evaluated : Evaluates (snapshotEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
    resolution.snapshot coreEnvironment) resolution.store (shift 3 lowered.expression) (.inRight .word value) store
  related : ValueRep checked.catalog signatures functions mapping world place.type right value prepared.route.leafType
  heaps : GenericHeap.HeapRepresents (payloadModel checked.catalog signatures functions) mapping world heap store
  maps : LocationMap.Extends resolution.mapping mapping
  worlds : WorldExtends resolution.world world
  frame : AdministrativePreserved resolution.mapping resolution.store mapping store
  metadata : Dynamic.HeapMetadataExtend targetHeap heap

inductive Result (checked : SourceCoreDataCatalog.Checked) (signatures : ProgramSignatures)
    (functions : GenericHeap.PayloadModel checked.catalog) (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (faults : FaultRep)
    (prepared : Prepared) (codes : List SourceCoreBasic.LoweredExpr) (sourceTypes : List TypeSystem.Ty)
    (place : PlaceResolution) (environment : Dynamic.Environment) (coreEnvironment : Environment)
    (before : Dynamic.Heap) (store : Store) (mapping : LocationMap) (world : StoreTyping)
    (rhs : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr) (next : Expr) (outputType : Ty)
    (operator : Syntax.ValueAssignOp) (invalid : Word) (result : Value) (finalStore : Store) : Prop where
  | fault {reason : Dynamic.SemanticFault} {token : Word} {after : Dynamic.Heap}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      (sourceFault : Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator rhs reason after)
      (resultEq : result = .inLeft outputType (.word token)) (tokenRep : faults reason token)
      (heaps : GenericHeap.HeapRepresents (payloadModel checked.catalog signatures functions) finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after) :
      Result checked signatures functions program context evidence source faults prepared codes sourceTypes place
        environment coreEnvironment before store mapping world rhs lowered next outputType operator invalid result finalStore
  | ready {target : Dynamic.ResolvedPlace} {targetHeap : Dynamic.Heap}
      (sourceTrace : Dynamic.SourcePlaceResolves program context evidence source environment before place target targetHeap)
      (resolution : DataPlaceResolvedTarget.Execution checked signatures functions prepared codes sourceTypes place target
        coreEnvironment store mapping world before targetHeap)
      (right : Execution checked signatures functions program context evidence source environment prepared codes sourceTypes place target
        coreEnvironment store mapping world before targetHeap resolution rhs lowered)
      (continuation : Evaluates (rhsEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
        resolution.snapshot right.value coreEnvironment) right.store
        (remainder prepared (SourceCoreCalls.packArguments codes).type next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) invalid) result finalStore) :
      Result checked signatures functions program context evidence source faults prepared codes sourceTypes place
        environment coreEnvironment before store mapping world rhs lowered next outputType operator invalid result finalStore

/-- Consume the output of whole-resolution reflection. Its RHS execution is
extracted from the actual remainder and reflected under exactly three hidden
slots. No child source trace, evaluation or exact-value weakening is assumed. -/
theorem reflects {checked : SourceCoreDataCatalog.Checked} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel checked.catalog} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {administrativeContext : Core.Context}
    (meaning : Reflects (payloadModel checked.catalog signatures functions) program context evidence source certificate faults)
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (sourceType : node.type = place.type) (coreType : lowered.type = prepared.route.leafType)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {coreEnvironment : Environment}
    {before : Dynamic.Heap} {store finalStore : Store}
    (environments : DataHeap.EnvRepresents checked.catalog mapping world administrativeContext scope environment coreEnvironment)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    {next : Expr} {outputType : Ty} {operator : Syntax.ValueAssignOp} {invalid : Word} {result : Value}
    (resolution : DataPlacePrefixReflection.Result checked signatures functions program context evidence source faults prepared codes sourceTypes place
      environment coreEnvironment before store mapping world lowered.expression next outputType
      (binaryOperator (prepared.route.leafType = .integer) operator) false invalid result finalStore) :
    Result checked signatures functions program context evidence source faults prepared codes sourceTypes place environment
      coreEnvironment before store mapping world id lowered next outputType operator invalid result finalStore := by
  cases resolution with
  | fault sourceFault resultEq tokenRep heaps maps worlds frame metadata =>
    exact .fault (.target sourceFault) resultEq tokenRep heaps maps worlds frame metadata
  | resolved sourceTrace resolution remaining =>
    have sameEnvironment : ReadOnly.EnvironmentsAgree Renaming.id coreEnvironment coreEnvironment := by
      intro i value found; exact found
    have reflectRhs := fun {right : Value} {rhsStore : Store}
        (evaluated : Evaluates (snapshotEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
          resolution.snapshot coreEnvironment) resolution.store (shift 3 lowered.expression) right rhsStore) =>
      DataPlaceChildExpressions.reflects meaning generated found (environments.extend resolution.maps resolution.worlds)
        resolution.heaps (locals.mono resolution.metadata) sameEnvironment
        [resolution.snapshot, packValues resolution.values, .cellRef (OptionalCell.cellType prepared.route.rootType) resolution.target]
        (by simpa only [Expr.rename_id, List.length_cons, List.length_nil, List.cons_append, List.nil_append,
          snapshotEnvironment, keysEnvironment, referenceEnvironment] using evaluated)
    cases remaining with
    | caseLeft rhsEvaluated failed =>
      obtain ⟨outcome, rhsHeap, rhsMap, rhsWorld, sourceRhs, represented, rhsHeaps, maps, worlds, frame, metadata⟩ :=
        reflectRhs rhsEvaluated
      cases represented with
      | fault tokenRep =>
        cases sourceRhs with
        | fault sourceRhs =>
          cases failed with
          | inLeft valueEvaluated =>
            cases valueEvaluated with
            | var found =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at found
              subst_vars
              exact .fault (.rhs sourceTrace sourceRhs) rfl tokenRep rhsHeaps (resolution.maps.trans maps)
                (resolution.worlds.trans worlds) (resolution.frame.trans frame) (resolution.metadata.trans metadata)
    | caseRight rhsEvaluated remaining =>
      obtain ⟨outcome, rhsHeap, rhsMap, rhsWorld, sourceRhs, represented, rhsHeaps, maps, worlds, frame, metadata⟩ :=
        reflectRhs rhsEvaluated
      cases represented with
      | value payload =>
        cases sourceRhs with
        | value sourceRhs =>
          exact .ready sourceTrace resolution
            { right := _
              value := _
              heap := rhsHeap
              store := _
              mapping := rhsMap
              world := rhsWorld
              sourceTrace := sourceRhs
              evaluated := rhsEvaluated
              related := by simpa only [payloadModel, sourceType, coreType] using payload
              heaps := rhsHeaps
              maps := maps
              worlds := worlds
              frame := frame
              metadata := metadata }
            remaining

end Solcore.SourceSemantics.CoreLowering.DataPlaceRhsReflection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataPlaceTailReflection
/-! Reflection of the actual modifier, latest-root setter and final mapped
write. The input RHS execution is the semantic output of prefix/RHS reflection.
Successful assignment exposes the real seven-slot continuation; all failure
branches terminate before that continuation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlaceTailReflection
open Core Frontend Frontend.SourceInference GeneralHeap DataPatternValues DataPayload
open GenericExpressionMeaning SourceCoreDataPlaces DataPlaceExecution DataEquality

inductive Result (checked : SourceCoreDataCatalog.Checked) (signatures : ProgramSignatures)
    (functions : GenericHeap.PayloadModel checked.catalog) (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (faults : FaultRep)
    (place : PlaceResolution) (operator : Syntax.ValueAssignOp) (rhs : ExpressionId)
    (environment : Dynamic.Environment) (coreEnvironment : Environment)
    (before : Dynamic.Heap) (store : Store) (mapping : LocationMap) (world : StoreTyping)
    (next : Expr) (outputType : Ty) (result : Value) (finalStore : Store) : Prop where
  | fault {reason : Dynamic.SemanticFault} {token : Word} {after : Dynamic.Heap}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      (trace : Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator rhs reason after)
      (resultEq : result = .inLeft outputType (.word token)) (tokenRep : faults reason token)
      (heaps : GenericHeap.HeapRepresents (payloadModel checked.catalog signatures functions) finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after) :
      Result checked signatures functions program context evidence source faults place operator rhs environment coreEnvironment
        before store mapping world next outputType result finalStore
  | committed {updated : Dynamic.Value} {after : Dynamic.Heap} {written : Store}
      {finalMap : LocationMap} {finalWorld : StoreTyping} {slots : Environment}
      (trace : Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies operator)
        environment before place rhs updated after)
      (heaps : GenericHeap.HeapRepresents (payloadModel checked.catalog signatures functions) finalMap finalWorld after written)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap written) (metadata : Dynamic.HeapMetadataExtend before after)
      (length : slots.length = 7)
      (continuation : Evaluates (slots ++ coreEnvironment) written (shift 7 next) result finalStore) :
      Result checked signatures functions program context evidence source faults place operator rhs environment coreEnvironment
        before store mapping world next outputType result finalStore

private theorem initial_exists {catalog : SourceCoreDataCatalog.Catalog} {model : GenericHeap.PayloadModel catalog}
    {mapping : LocationMap} {world : StoreTyping} {cell : Dynamic.Cell} {optional : Value} {type : Ty}
    (related : GenericHeap.CellRepresents model mapping world cell optional type) :
    ∃ initial, Dynamic.RootInitialValue cell initial := by
  cases related with
  | initialized => exact ⟨_, .initialized⟩
  | @uninitialized sourceType _ projected =>
    by_cases mappingType : ∃ key value, sourceType = .mapping key value
    · obtain ⟨key, value, rfl⟩ := mappingType
      exact ⟨_, .emptyMapping key value⟩
    · exact ⟨none, .uninitialized mappingType⟩

private theorem missing_token {faults : FaultRep} {missing : TypeSystem.Ty → Word}
    (tokens : ∀ type, faults (.missingMappingDefault type) (missing type))
    {initial : Option Dynamic.Value} {projections : List Dynamic.EvaluatedProjection} {reason : Dynamic.SemanticFault}
    (fault : Dynamic.ProjectionsFaults initial projections reason) : faults reason (DataPlaceExactFault.token missing reason) := by
  induction fault with
  | indexDefaultUnavailable => exact tokens _
  | indexFound _ _ _ ih | indexDefault _ _ _ _ ih | member _ _ ih => exact ih

/-- Complete the already reflected target and RHS. Source traversal order is
respected even though Core computes the scalar modifier first: initialized
modifiers succeed, while an absent snapshot implies an empty source path. -/
theorem reflects_ready {checked : SourceCoreDataCatalog.Checked} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel checked.catalog} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
    {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {administrativeContext : Core.Context}
    (functionTypes : FunctionRuntimeTypes functions) (layouts : CatalogLayouts checked.catalog)
    {identities : Dynamic.Value → Word → Prop}
    (observations : FunctionObservations checked.catalog signatures functions identities) (faithful : IdentityFaithful identities)
    {steps : List Step}
    (raw : DataPlaceRouteCertificates.RawPath checked signatures source prepared.route.rootSourceType prepared.route.rootType
      steps place.projections place.type prepared.route.leafType sourceTypes)
    {fuel : Nat} {missing : TypeSystem.Ty → Word}
    (preparation : DataPlaceMappingPreparation.Steps checked fuel missing 0 steps prepared.steps prepared.keys)
    (rootLayout : DataPlaceSnapshot.RootLayout checked.catalog prepared prepared.route.rootSourceType)
    (keyTypes : prepared.keyTypes = codes.map (·.type))
    [FunctionCalls.FaultTokens faults]
    (missingTokens : ∀ type, faults (.missingMappingDefault type) (missing type))
    {operator : Syntax.ValueAssignOp} {invalid : Word}
    (operatorProfile : operator = .equal ∨ place.type = .word ∨ place.type = .integer ∧ operator.wordOnly = false)
    (invalidToken : faults (.invalidAssignmentOperands operator) invalid)
    (setterTyped : HasType
      (prepared.route.leafType :: prepared.route.leafType :: prepared.optionalLeaf :: (SourceCoreCalls.packArguments codes).type ::
        OptionalCell.referenceType prepared.route.rootType :: (SourceCoreLocalCell.coreContext scope ++ administrativeContext))
      (.apply (setter prepared (SourceCoreCalls.packArguments codes).type) (.pair (.loadCell (.var 4)) (.pair (.var 3) (.var 0))))
      (LanguageResult.resultType prepared.route.rootType) checked.catalog.definitions)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {coreEnvironment : Environment}
    {before targetHeap : Dynamic.Heap} {store finalStore : Store}
    (environments : DataHeap.EnvRepresents checked.catalog mapping world administrativeContext scope environment coreEnvironment)
    {target : Dynamic.ResolvedPlace}
    (sourceTrace : Dynamic.SourcePlaceResolves program context evidence source environment before place target targetHeap)
    (rootType : target.rootType = prepared.route.rootSourceType)
    (resolution : DataPlaceResolvedTarget.Execution checked signatures functions prepared codes sourceTypes place target
      coreEnvironment store mapping world before targetHeap)
    {rhs : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (right : DataPlaceRhsReflection.Execution checked signatures functions program context evidence source environment prepared codes sourceTypes place target
      coreEnvironment store mapping world before targetHeap resolution rhs lowered)
    {next : Expr} {outputType : Ty} {result : Value}
    (completed : Evaluates (rhsEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
        resolution.snapshot right.value coreEnvironment) right.store
      (DataPlaceRhsReflection.remainder prepared (SourceCoreCalls.packArguments codes).type next outputType
        (binaryOperator (prepared.route.leafType = .integer) operator) invalid) result finalStore) :
    Result checked signatures functions program context evidence source faults place operator rhs environment coreEnvironment
      before store mapping world next outputType result finalStore := by
  have snapshotRep := resolution.snapshotRelated.extend right.maps right.worlds
  have keysRep := resolution.keysRelated.extend right.maps right.worlds
  have reference := resolution.reference.extend right.maps right.worlds
  have oldRead : ∃ cell, Dynamic.Heap.Reads targetHeap target.location cell ∧ cell.type = target.rootType := by
    cases sourceTrace with
    | intro _ _ _ read _ _ => exact ⟨_, read, rfl⟩
  obtain ⟨oldCell, oldRead, oldType⟩ := oldRead
  obtain ⟨cell, currentRead, currentType, _⟩ := right.metadata target.location oldCell oldRead
  have cellType : cell.type = target.rootType := currentType.trans oldType
  have sourceType : cell.type = prepared.route.rootSourceType := cellType.trans rootType
  have currentRaw : DataPlaceRouteCertificates.RawPath checked signatures source cell.type prepared.route.rootType
      steps place.projections place.type prepared.route.leafType sourceTypes := by rw [sourceType]; exact raw
  have currentLayout : DataPlaceSnapshot.RootLayout checked.catalog prepared cell.type := by rw [sourceType]; exact rootLayout
  have keyLength : prepared.keyTypes.length = resolution.values.length := keyTypes ▸ keysRep.length.2
  cases completed with
  | caseLeft modifiedEvaluated failed =>
    obtain ⟨sameStore, represented⟩ := DataPlaceModifierReflection.reflects operatorProfile snapshotRep right.related
      (.var (index := 1) rfl) (.var (index := 0) rfl) modifiedEvaluated
    subst_vars
    cases represented with
    | uninitialized absent notEqual =>
      have empty := DataPlaceSourceOrder.resolve_none sourceTrace absent
      obtain ⟨_, _, cellRep⟩ := DataPlaceSnapshot.read_at right.heaps reference currentRead
      obtain ⟨initial, root⟩ := initial_exists cellRep
      have read : Dynamic.ProjectionsRead initial target.projections initial := empty ▸ .nil
      have fault : Dynamic.AssignmentOperandsInvalid operator target.selected right.right := absent ▸ .uninitialized notEqual
      cases failed with
      | inLeft valueEvaluated =>
        cases valueEvaluated with
        | var found =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at found
          subst_vars
          exact .fault (.operands sourceTrace right.sourceTrace currentRead cellType root read fault) rfl invalidToken
            right.heaps (resolution.maps.trans right.maps) (resolution.worlds.trans right.worlds)
            (resolution.frame.trans right.frame) (resolution.metadata.trans right.metadata)
  | caseRight modifiedEvaluated remaining =>
    rename_i modifiedStore modifiedType modifiedValue
    obtain ⟨sameStore, represented⟩ := DataPlaceModifierReflection.reflects operatorProfile snapshotRep right.related
      (.var (index := 1) rfl) (.var (index := 0) rfl) modifiedEvaluated
    subst_vars
    cases represented with
    | @applied replacement _ applies replacementRep =>
      have typedEnvironment : RuntimeEnvironmentHasTypes right.world
          (modifiedEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
            resolution.snapshot right.value modifiedValue coreEnvironment)
          (prepared.route.leafType :: prepared.route.leafType :: prepared.optionalLeaf :: (SourceCoreCalls.packArguments codes).type ::
            OptionalCell.referenceType prepared.route.rootType :: (SourceCoreLocalCell.coreContext scope ++ administrativeContext))
          checked.catalog.definitions :=
        .cons replacementRep.runtime_hasType (.cons right.related.runtime_hasType (.cons snapshotRep.runtime_hasType
          (.cons (DataPlaceResolvedTarget.values_typed keysRep) (.cons (.cellRef reference.typed)
            ((environments.extend (resolution.maps.trans right.maps) (resolution.worlds.trans right.worlds)).runtime_hasTypes)))))
      have reflectSetter := fun {actual : Value} {after : Store}
          (ran : Evaluates (modifiedEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
              resolution.snapshot right.value modifiedValue coreEnvironment) right.store
            (.apply (setter prepared (SourceCoreCalls.packArguments codes).type) (.pair (.loadCell (.var 4)) (.pair (.var 3) (.var 0)))) actual after) =>
        DataPlaceSetterReflection.reflects_at functionTypes layouts observations faithful currentRaw preparation
          resolution.shaped keysRep keyLength currentLayout replacementRep right.heaps reference currentRead
          typedEnvironment setterTyped (.var rfl) (.var rfl) (.var rfl) ran
      cases remaining with
      | caseLeft setterEvaluated failed =>
        obtain ⟨futureWorld, administrative, represented, extension, finalHeaps, _, frame, _⟩ := reflectSetter setterEvaluated
        cases represented with
        | missing root fault =>
          cases failed with
          | inLeft valueEvaluated =>
            cases valueEvaluated with
            | var found =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at found
              subst_vars
              exact .fault (.structuralUpdate sourceTrace right.sourceTrace currentRead cellType root fault) rfl
                (missing_token missingTokens fault) finalHeaps (resolution.maps.trans right.maps)
                ((resolution.worlds.trans right.worlds).trans extension)
                ((resolution.frame.trans right.frame).trans frame) (resolution.metadata.trans right.metadata)
        | uninitialized root nonempty =>
          exact (DataPlaceSourceOrder.latest_uninitialized_impossible sourceTrace right.sourceTrace currentRead cellType root nonempty).elim
      | caseRight setterEvaluated remaining =>
        rename_i helperStore helperType updatedValue
        obtain ⟨futureWorld, administrative, represented, extension, helperHeaps, _, helperFrame, _⟩ := reflectSetter setterEvaluated
        cases represented with
        | @updated initial updated _ root changed updatedRep =>
          rcases SourceCoreDataPlaces.guard_inv remaining with ⟨_, remaining⟩ | ⟨operation, selected, zero, _, _⟩
          · cases remaining with
            | letE writeEvaluated continuation =>
              obtain ⟨after, resultEq, sourceWritten, finalHeaps, writeFrame, metadata, _⟩ :=
                DataPlaceCommitReflection.reflects_storeCell helperHeaps (reference.extend (.refl _) extension) currentRead
                  updatedRep (.var (index := 5) rfl) (.var (index := 0) rfl) writeEvaluated
              subst_vars
              have changed := DataPlaceCommitReflection.update_of_replacement changed (fun _ => applies)
              exact .committed (.intro sourceTrace right.sourceTrace (.intro currentRead cellType root changed sourceWritten))
                finalHeaps (resolution.maps.trans right.maps) ((resolution.worlds.trans right.worlds).trans extension)
                (((resolution.frame.trans right.frame).trans helperFrame).trans writeFrame)
                ((resolution.metadata.trans right.metadata).trans metadata) (slots :=
                  [.unit, updatedValue, modifiedValue, right.value, resolution.snapshot, packValues resolution.values,
                    .cellRef (OptionalCell.cellType prepared.route.rootType) resolution.target]) rfl continuation
          · -- An applied source operation has a nonzero divisor, so the check passed.
            have panics := DataPlaceModifier.binaryOperator_panics selected
            have rightRep := right.related
            rw [DataPlaceModifier.panicking_word operatorProfile panics] at rightRep
            obtain ⟨word, sourceWord, coreWord⟩ := DataPlaceModifier.word_rep rightRep
            rw [zero] at coreWord
            cases coreWord
            rcases DataPlaceModifier.assignment_divisor applies with total | different
            · rw [panics] at total; cases total
            · exact (different sourceWord).elim
    | @panicking replacement _ operation zero selected panicked replacementRep =>
      have typedEnvironment : RuntimeEnvironmentHasTypes right.world
          (modifiedEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
            resolution.snapshot right.value modifiedValue coreEnvironment)
          (prepared.route.leafType :: prepared.route.leafType :: prepared.optionalLeaf :: (SourceCoreCalls.packArguments codes).type ::
            OptionalCell.referenceType prepared.route.rootType :: (SourceCoreLocalCell.coreContext scope ++ administrativeContext))
          checked.catalog.definitions :=
        .cons replacementRep.runtime_hasType (.cons right.related.runtime_hasType (.cons snapshotRep.runtime_hasType
          (.cons (DataPlaceResolvedTarget.values_typed keysRep) (.cons (.cellRef reference.typed)
            ((environments.extend (resolution.maps.trans right.maps) (resolution.worlds.trans right.worlds)).runtime_hasTypes)))))
      have reflectSetter := fun {actual : Value} {after : Store}
          (ran : Evaluates (modifiedEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
              resolution.snapshot right.value modifiedValue coreEnvironment) right.store
            (.apply (setter prepared (SourceCoreCalls.packArguments codes).type) (.pair (.loadCell (.var 4)) (.pair (.var 3) (.var 0)))) actual after) =>
        DataPlaceSetterReflection.reflects_at functionTypes layouts observations faithful currentRaw preparation
          resolution.shaped keysRep keyLength currentLayout replacementRep right.heaps reference currentRead
          typedEnvironment setterTyped (.var rfl) (.var rfl) (.var rfl) ran
      cases remaining with
      | caseLeft setterEvaluated failed =>
        obtain ⟨futureWorld, administrative, represented, extension, finalHeaps, _, frame, _⟩ := reflectSetter setterEvaluated
        cases represented with
        | missing root fault =>
          cases failed with
          | inLeft valueEvaluated =>
            cases valueEvaluated with
            | var found =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at found
              subst_vars
              exact .fault (.structuralUpdate sourceTrace right.sourceTrace currentRead cellType root fault) rfl
                (missing_token missingTokens fault) finalHeaps (resolution.maps.trans right.maps)
                ((resolution.worlds.trans right.worlds).trans extension)
                ((resolution.frame.trans right.frame).trans frame) (resolution.metadata.trans right.metadata)
        | uninitialized root nonempty =>
          exact (DataPlaceSourceOrder.latest_uninitialized_impossible sourceTrace right.sourceTrace currentRead cellType root nonempty).elim
      | caseRight setterEvaluated remaining =>
        rename_i helperStore helperType updatedValue
        obtain ⟨futureWorld, administrative, represented, extension, helperHeaps, _, helperFrame, _⟩ := reflectSetter setterEvaluated
        cases represented with
        | @updated initial updated _ root changed updatedRep =>
          -- The latest root is traversable, so the source panics on its operands.
          obtain ⟨_, read⟩ := changed.readable
          have rightRep := right.related
          rw [DataPlaceModifier.panicking_word operatorProfile (DataPlaceModifier.binaryOperator_panics selected), zero]
            at rightRep
          obtain ⟨_, sourceWord, coreWord⟩ := DataPlaceModifier.word_rep rightRep
          cases sourceWord
          rcases SourceCoreDataPlaces.guard_inv remaining with ⟨passes, _⟩ | ⟨_, _, _, resultEq, storeEq⟩
          · rw [selected, coreWord] at passes
            cases passes with
            | total total => cases total _ rfl
            | nonzero nonzero => exact (nonzero rfl).elim
          · subst resultEq storeEq
            exact .fault (.panic sourceTrace right.sourceTrace currentRead cellType root read panicked) rfl
              (FunctionCalls.FaultTokens.panic _) helperHeaps (resolution.maps.trans right.maps)
              ((resolution.worlds.trans right.worlds).trans extension)
              ((resolution.frame.trans right.frame).trans helperFrame) (resolution.metadata.trans right.metadata)

end Solcore.SourceSemantics.CoreLowering.DataPlaceTailReflection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataPlaceAssignmentReflection
/-! Whole execute reflection from static compilation receipts and a universal
child-expression theorem. Key/RHS/getter/modifier/setter evaluations and source
traces are all extracted or constructed here, never certificate assumptions.
The remaining statement continuation is exposed under its real seven slots. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlaceAssignmentReflection
open Core Frontend Frontend.SourceInference GeneralHeap DataPayload
open GenericExpressionMeaning SourceCoreDataPlaces

theorem reflects {checked : SourceCoreDataCatalog.Checked} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel checked.catalog} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {administrativeContext : Core.Context}
    (layout : DataPlaceResolvedTarget.Layout checked signatures functions source certificate scope place prepared codes sourceTypes
      (SourceCoreLocalCell.coreContext scope ++ administrativeContext))
    {steps : List Step} {fuel : Nat} {missing : TypeSystem.Ty → Word}
    (raw : DataPlaceRouteCertificates.RawPath checked signatures source prepared.route.rootSourceType prepared.route.rootType
      steps place.projections place.type prepared.route.leafType sourceTypes)
    (preparation : DataPlaceMappingPreparation.Steps checked fuel missing 0 steps prepared.steps prepared.keys)
    (meaning : Reflects (payloadModel checked.catalog signatures functions) program context evidence source certificate faults)
    (functionTypes : FunctionRuntimeTypes functions) (layouts : CatalogLayouts checked.catalog)
    {identities : Dynamic.Value → Word → Prop}
    (observations : FunctionObservations checked.catalog signatures functions identities) (faithful : DataEquality.IdentityFaithful identities)
    [FunctionCalls.FaultTokens faults]
    (missingTokens : ∀ type, faults (.missingMappingDefault type) (missing type))
    {rhs : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (rhsGenerated : certificate scope rhs lowered) (found : source.lookupExpression? rhs = some node)
    (rhsSourceType : node.type = place.type) (rhsCoreType : lowered.type = prepared.route.leafType)
    {operator : Syntax.ValueAssignOp} {invalid : Word}
    (operatorProfile : operator = .equal ∨ place.type = .word ∨ place.type = .integer ∧ operator.wordOnly = false)
    (invalidOperandToken : faults (.invalidAssignmentOperands operator) invalid)
    (setterTyped : HasType
      (prepared.route.leafType :: prepared.route.leafType :: prepared.optionalLeaf :: (SourceCoreCalls.packArguments codes).type ::
        OptionalCell.referenceType prepared.route.rootType :: (SourceCoreLocalCell.coreContext scope ++ administrativeContext))
      (.apply (setter prepared (SourceCoreCalls.packArguments codes).type) (.pair (.loadCell (.var 4)) (.pair (.var 3) (.var 0))))
      (LanguageResult.resultType prepared.route.rootType) checked.catalog.definitions)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {coreEnvironment : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {sourceLocation : Dynamic.Location} {initialCell : Dynamic.Cell} {index : Nat}
    (environments : DataHeap.EnvRepresents checked.catalog mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GenericHeap.HeapRepresents (payloadModel checked.catalog signatures functions) mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (lookup : Dynamic.Environment.LooksUp environment place.root sourceLocation)
    (initialRead : Dynamic.Heap.Reads before sourceLocation initialCell)
    (rootType : initialCell.type = prepared.route.rootSourceType)
    (invalidProjectionToken : faults (.uninitializedLocation sourceLocation) prepared.invalidProjection)
    {next : Expr} {outputType : Ty} {result : Value}
    (completed : Evaluates coreEnvironment store
      (execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression next outputType
        (binaryOperator (prepared.route.leafType = .integer) operator) false invalid) result finalStore) :
    DataPlaceTailReflection.Result checked signatures functions program context evidence source faults place operator rhs
      environment coreEnvironment before store mapping world next outputType result finalStore := by
  have resolution := DataPlacePrefixReflection.reflects layout raw preparation meaning functionTypes layouts observations faithful
    missingTokens environments heaps locals slot lookup initialRead rootType invalidProjectionToken completed
  have rhs := DataPlaceRhsReflection.reflects meaning rhsGenerated found rhsSourceType rhsCoreType environments locals resolution
  cases rhs with
  | fault sourceFault resultEq tokenRep heaps maps worlds frame metadata =>
    exact .fault sourceFault resultEq tokenRep heaps maps worlds frame metadata
  | ready sourceTrace resolution right continuation =>
    have targetType := (DataPlaceSourceOrder.resolve_root_type sourceTrace resolution.metadata lookup initialRead).trans rootType
    exact DataPlaceTailReflection.reflects_ready functionTypes layouts observations faithful raw preparation layout.root layout.keyTypes
      missingTokens operatorProfile invalidOperandToken setterTyped environments sourceTrace targetType resolution right continuation

end Solcore.SourceSemantics.CoreLowering.DataPlaceAssignmentReflection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataPlaceAssignmentSuccess
/-! Success of the full emitted assignment transaction. Child expressions use
their universal semantic IH; getter, modifier, latest-root setter and mapped
write are derived. The terminal continuation returns Unit. Statement-list
induction and automatic extraction of every static path layout remain separate.
-/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlaceAssignmentSuccess
open Core Frontend Frontend.SourceInference GeneralHeap DataPatternValues DataPayload
open GenericExpressionMeaning SourceCoreDataPlaces DataPlaceExecution

theorem modifier_preserves {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel catalog} {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {type : Ty} {snapshot : Option Dynamic.Value}
    {right result : Dynamic.Value} {snapshotCore rightCore : Value} {operator : Syntax.ValueAssignOp}
    (profile : operator = .equal ∨ sourceType = .word ∨ sourceType = .integer ∧ operator.wordOnly = false)
    (snapshotRep : DataPlaceSnapshot.OptionalRep catalog signatures functions mapping world sourceType type snapshot snapshotCore)
    (rightRep : ValueRep catalog signatures functions mapping world sourceType right rightCore type)
    (applied : Dynamic.AssignmentValueApplies operator snapshot right result)
    {environment : Environment} {snapshotExpression rightExpression : Expr}
    (snapshotSelected : DataEquality.Selects environment snapshotExpression snapshotCore)
    (rightSelected : DataEquality.Selects environment rightExpression rightCore) (store : Store) (invalid : Word) :
    ∃ value, ValueRep catalog signatures functions mapping world sourceType result value type ∧
      Evaluates environment store
        (modified type (binaryOperator (type = .integer) operator) false snapshotExpression rightExpression invalid)
        (.inRight .word value) store := by
  by_cases equal : operator = .equal
  · subst operator
    cases applied
    exact ⟨rightCore, rightRep, DataPlaceModifier.equal_modified rightSelected store invalid⟩
  · have numeric : sourceType = .word ∨ sourceType = .integer ∧ operator.wordOnly = false := profile.resolve_left equal
    cases snapshotRep with
    | absent => cases applied; exact (equal rfl).elim
    | present represented =>
      obtain ⟨value, resultRep, evaluated, _⟩ := DataPlaceModifier.initialized_preserves numeric represented rightRep
        applied snapshotSelected rightSelected store invalid
      exact ⟨value, resultRep, evaluated⟩

/-- A successful independently specified source assignment has a matching
whole Core execution. No actual key/RHS/helper evaluation is a premise.
The complete payload relation retains callable leaves and ordered mapping keys.
Static helper typing and path-layout receipts remain explicit obligations. -/
theorem preserves {checked : SourceCoreDataCatalog.Checked} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel checked.catalog} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty}
    {administrativeContext : Core.Context}
    (layout : DataPlaceResolvedTarget.Layout checked signatures functions source certificate scope place prepared codes sourceTypes
      (SourceCoreLocalCell.coreContext scope ++ administrativeContext))
    (meaning : Preserves (payloadModel checked.catalog signatures functions) program context evidence source certificate faults)
    {identities : Dynamic.Value → Word → Prop}
    (observations : FunctionObservations checked.catalog signatures functions identities)
    (faithful : DataEquality.IdentityFaithful identities) (layouts : CatalogLayouts checked.catalog)
    {rhs : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (rhsGenerated : certificate scope rhs lowered) (found : source.lookupExpression? rhs = some node)
    (rhsSourceType : node.type = place.type) (rhsCoreType : lowered.type = prepared.route.leafType)
    {operator : Syntax.ValueAssignOp}
    (operatorProfile : operator = .equal ∨ place.type = .word ∨ place.type = .integer ∧ operator.wordOnly = false)
    (setterTyped : HasType
      (prepared.route.leafType :: prepared.route.leafType :: prepared.optionalLeaf :: (SourceCoreCalls.packArguments codes).type ::
        OptionalCell.referenceType prepared.route.rootType :: (SourceCoreLocalCell.coreContext scope ++ administrativeContext))
      (.apply (setter prepared (SourceCoreCalls.packArguments codes).type) (.pair (.loadCell (.var 4)) (.pair (.var 3) (.var 0))))
      (LanguageResult.resultType prepared.route.rootType) checked.catalog.definitions)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {coreEnvironment : Environment}
    {before targetHeap rhsHeap after : Dynamic.Heap} {store : Store} {sourceTarget : Dynamic.ResolvedPlace} {index : Nat}
    {right updatedRoot : Dynamic.Value}
    (environments : DataHeap.EnvRepresents checked.catalog mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GenericHeap.HeapRepresents (payloadModel checked.catalog signatures functions) mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootType : sourceTarget.rootType = prepared.route.rootSourceType)
    (resolve : Dynamic.SourcePlaceResolves program context evidence source environment before place sourceTarget targetHeap)
    (evaluate : Dynamic.ExpressionEvaluates program context evidence source environment targetHeap rhs right rhsHeap)
    (written : Dynamic.ResolvedPlaceWrites
      (fun _ updated => Dynamic.AssignmentValueApplies operator sourceTarget.selected right updated)
      rhsHeap sourceTarget updatedRoot after)
    (invalidOperand : Word) :
    ∃ updatedValue finalStore finalMap finalWorld,
      Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies operator)
        environment before place rhs updatedRoot after ∧
      Evaluates coreEnvironment store
        (execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression (LanguageResult.success .unit) .unit
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalidOperand)
        (.inRight .word .unit) finalStore ∧
      ValueRep checked.catalog signatures functions finalMap finalWorld prepared.route.rootSourceType updatedRoot updatedValue prepared.route.rootType ∧
      GenericHeap.HeapRepresents (payloadModel checked.catalog signatures functions) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  have sourceAssignment := Dynamic.SourcePlaceAssignment.intro resolve evaluate written
  obtain ⟨target, coreLookup⟩ := DataPlaceResolvedTarget.preserves layout meaning observations faithful layouts
    environments heaps locals slot rootType resolve
  have sameEnvironment : ReadOnly.EnvironmentsAgree Renaming.id coreEnvironment coreEnvironment := by
    intro i v selected; exact selected
  obtain ⟨rightValue, rhsStore, rhsMap, rhsWorld, evaluated, rightRep, rhsHeaps, rhsMaps, rhsWorlds, rhsFrame, rhsMetadata⟩ :=
    DataPlaceChildExpressions.preserves meaning rhsGenerated found
      (environments.extend target.maps target.worlds) target.heaps (locals.mono target.metadata) sameEnvironment
      [target.snapshot, packValues target.values, .cellRef (OptionalCell.cellType prepared.route.rootType) target.target]
      (.value evaluate)
  cases rightRep with
  | @value _ rightValue rightRep =>
    have rhsEvaluated : Evaluates
        (snapshotEnvironment prepared.route.rootType target.target (packValues target.values) target.snapshot coreEnvironment)
        target.store (shift 3 lowered.expression) (.inRight .word rightValue) rhsStore := by
      simpa only [Expr.rename_id, List.length_cons, List.length_nil, List.cons_append, List.nil_append,
        snapshotEnvironment, keysEnvironment, referenceEnvironment] using evaluated
    have rightRep : ValueRep checked.catalog signatures functions rhsMap rhsWorld place.type right rightValue prepared.route.leafType := by
      simpa only [payloadModel, rhsSourceType, rhsCoreType] using rightRep
    have snapshotRep := target.snapshotRelated.extend rhsMaps rhsWorlds
    have keyRep := target.keysRelated.extend rhsMaps rhsWorlds
    have reference := target.reference.extend rhsMaps rhsWorlds
    cases written with
    | @intro _ _ cell initial _ sourceRead cellType initialValue update sourceWrite =>
      obtain ⟨replacement, applies, changed⟩ := DataPlaceAssignmentWriteBack.replacement_of_update update
      obtain ⟨replacementValue, replacementRep, modifiedEvaluated⟩ :=
        modifier_preserves operatorProfile snapshotRep rightRep applies
          (environment := rhsEnvironment prepared.route.rootType target.target (packValues target.values)
            target.snapshot rightValue coreEnvironment) (.var (index := 1) rfl) (.var (index := 0) rfl) rhsStore invalidOperand
      obtain ⟨count, path⟩ := layout.paths target.shaped keyRep
      have sourceType : cell.type = prepared.route.rootSourceType := cellType.trans rootType
      have rootLayout : DataPlaceSnapshot.RootLayout checked.catalog prepared cell.type := by
        simpa only [sourceType] using layout.root
      have currentPath : DataPayloadReadPaths.Path checked signatures functions rhsMap rhsWorld target.values
          cell.type prepared.route.rootType prepared.steps sourceTarget.projections place.type prepared.route.leafType count := by
        simpa only [sourceType] using path
      have keyLength : prepared.keyTypes.length = target.values.length := layout.keyTypes ▸ keyRep.length.2
      have typedEnvironment : RuntimeEnvironmentHasTypes rhsWorld
          (modifiedEnvironment prepared.route.rootType target.target (packValues target.values) target.snapshot rightValue replacementValue coreEnvironment)
          (prepared.route.leafType :: prepared.route.leafType :: prepared.optionalLeaf :: (SourceCoreCalls.packArguments codes).type ::
            OptionalCell.referenceType prepared.route.rootType :: (SourceCoreLocalCell.coreContext scope ++ administrativeContext))
          checked.catalog.definitions :=
        .cons replacementRep.runtime_hasType (.cons rightRep.runtime_hasType (.cons snapshotRep.runtime_hasType
          (.cons (DataPlaceResolvedTarget.values_typed keyRep) (.cons (.cellRef reference.typed)
            ((environments.extend (target.maps.trans rhsMaps) (target.worlds.trans rhsWorlds)).runtime_hasTypes)))))
      obtain ⟨updatedValue, helperStore, finalStore, finalWorld, old, updatedRep, setterEvaluated,
        helperRead, coreWritten, extension, finalHeaps, frame, metadata⟩ :=
        DataPlaceAssignmentWriteBack.preserves observations faithful layouts prepared keyLength rhsHeaps reference sourceRead
          rootLayout initialValue changed sourceWrite currentPath replacementRep typedEnvironment setterTyped
          (.var rfl) (.var rfl) (.var rfl)
      refine ⟨updatedValue, finalStore, rhsMap, finalWorld, sourceAssignment, ?_,
        by simpa only [sourceType] using updatedRep, finalHeaps, target.maps.trans rhsMaps,
        (target.worlds.trans rhsWorlds).trans extension, (target.frame.trans rhsFrame).trans frame,
        (target.metadata.trans rhsMetadata).trans metadata⟩
      apply execute_success (.var coreLookup) target.keysEvaluated target.snapshotEvaluated rhsEvaluated
        modifiedEvaluated setterEvaluated
        (DataPlaceModifier.passes_of_applies operatorProfile rightRep applies _) helperRead coreWritten
      simpa only [shift, List.range, List.range.loop, List.foldl, Expr.weakenAt, LanguageResult.success] using
        (Evaluates.inRight (environment := writtenEnvironment prepared.route.rootType target.target
          (packValues target.values) target.snapshot rightValue replacementValue updatedValue coreEnvironment)
          (initialStore := finalStore) (leftType := .word) Evaluates.unit)

end Solcore.SourceSemantics.CoreLowering.DataPlaceAssignmentSuccess
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataPlaceContinuation
/-! A completed assignment prefix can be followed by a universally certified
expression under execute's seven real administrative values. Closure captures
use that actual extended environment; no exact-value weakening is assumed.
-/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlaceContinuation
open Core Frontend Frontend.SourceInference GeneralHeap DataPatternValues DataPayload
open GenericExpressionMeaning SourceCoreDataPlaces

/-- Successful terminal Unit exposes the actual seven values and admits an
arbitrary continuation at the resulting store. All prefix evaluations are
reused exactly once, including the latest-root load and final write. -/
theorem plug {prepared : Prepared} {reference rhs : Expr} {keys : SourceCoreBasic.LoweredExpr}
    {operator : Option Frontend.SourceCoreDataPlaces.Modifier} {bitNot : Bool} {invalid : Word}
    {environment : Environment} {before after : Store}
    (completed : Evaluates environment before
      (execute prepared reference keys rhs (LanguageResult.success .unit) .unit operator bitNot invalid)
      (.inRight .word .unit) after) :
    ∃ slots : Environment, slots.length = 7 ∧
      ∀ {next : Expr} {outputType : Ty} {value : Value} {finalStore : Store},
        Evaluates (slots ++ environment) after (shift 7 next) value finalStore →
        Evaluates environment before (execute prepared reference keys rhs next outputType operator bitNot invalid) value finalStore := by
  cases completed with
  | letE referenceEvaluated tail =>
    rename_i referenceStore referenceValue
    cases tail with
    | caseLeft _ impossible => cases impossible
    | caseRight keysEvaluated tail =>
      rename_i keyStore keyType keyValue
      cases tail with
      | caseLeft _ impossible => cases impossible
      | caseRight snapshotEvaluated tail =>
        rename_i snapshotStore snapshotType snapshotValue
        cases tail with
        | caseLeft _ impossible => cases impossible
        | caseRight rhsEvaluated tail =>
          rename_i rhsStore rhsType rightValue
          cases tail with
          | caseLeft _ impossible => cases impossible
          | caseRight modifiedEvaluated tail =>
            rename_i modifiedStore modifiedType modifiedValue
            cases tail with
            | caseLeft _ impossible => cases impossible
            | caseRight setterEvaluated tail =>
              rename_i setterStore setterType updatedValue
              rcases guard_inv tail with ⟨passes, tail⟩ | ⟨_, _, _, impossible, _⟩
              · cases tail with
                | letE writeEvaluated terminal =>
                  rename_i writtenStore writtenValue
                  simp only [shift, List.range, List.range.loop, List.foldl, Expr.weakenAt, LanguageResult.success] at terminal
                  cases terminal with
                  | inRight unitEvaluated =>
                    cases unitEvaluated
                    refine ⟨[writtenValue, updatedValue, modifiedValue, rightValue, snapshotValue, keyValue, referenceValue], rfl, ?_⟩
                    intro next outputType value finalStore continuation
                    exact .letE referenceEvaluated (.caseRight keysEvaluated (.caseRight snapshotEvaluated
                      (.caseRight rhsEvaluated (.caseRight modifiedEvaluated (.caseRight setterEvaluated
                        (guard_passes passes (.letE writeEvaluated continuation)))))))
              · cases impossible

/-- A universal expression IH supplies the continuation evaluation at the
actual temporary slots. `completed` is an already proved assignment result,
not a child-runtime assumption or a field of a static compilation receipt. -/
theorem preserves {catalog : SourceCoreDataCatalog.Catalog} {model : GenericHeap.PayloadModel catalog}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {certificate : Certificate} {faults : FaultRep}
    (meaning : Preserves model program context evidence source certificate faults)
    {scope : Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    {prepared : Prepared} {reference rhs : Expr} {keys : SourceCoreBasic.LoweredExpr}
    {operator : Option Frontend.SourceCoreDataPlaces.Modifier} {bitNot : Bool} {invalid : Word}
    {coreEnvironment : Environment} {initialStore store : Store}
    (completed : Evaluates coreEnvironment initialStore
      (execute prepared reference keys rhs (LanguageResult.success .unit) .unit operator bitNot invalid)
      (.inRight .word .unit) store)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates coreEnvironment initialStore
        (execute prepared reference keys rhs lowered.expression lowered.type operator bitNot invalid) value finalStore ∧
      ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨slots, length, finish⟩ := plug completed
  have sameEnvironment : ReadOnly.EnvironmentsAgree Renaming.id coreEnvironment coreEnvironment := by
    intro i v selected; exact selected
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, rest⟩ :=
    DataPlaceChildExpressions.preserves meaning generated found environments heaps locals sameEnvironment slots trace
  exact ⟨value, finalStore, finalMap, finalWorld,
    finish (by simpa only [length, Expr.rename_id] using evaluated), rest⟩

/-- Full source-to-Core composition for an assignment followed by a certified
expression. The completed prefix passed to the algebraic plugging law above
is constructed here from source semantics, never assumed by the caller. -/
theorem preserves_from_source {checked : SourceCoreDataCatalog.Checked} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel checked.catalog} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty}
    {administrativeContext : Core.Context}
    (layout : DataPlaceResolvedTarget.Layout checked signatures functions source certificate scope place prepared codes sourceTypes
      (SourceCoreLocalCell.coreContext scope ++ administrativeContext))
    (meaning : Preserves (payloadModel checked.catalog signatures functions) program context evidence source certificate faults)
    {identities : Dynamic.Value → Word → Prop}
    (observations : FunctionObservations checked.catalog signatures functions identities)
    (faithful : DataEquality.IdentityFaithful identities) (layouts : CatalogLayouts checked.catalog)
    {rhs : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (rhsGenerated : certificate scope rhs lowered) (found : source.lookupExpression? rhs = some node)
    (rhsSourceType : node.type = place.type) (rhsCoreType : lowered.type = prepared.route.leafType)
    {operator : Syntax.ValueAssignOp}
    (operatorProfile : operator = .equal ∨ place.type = .word ∨ place.type = .integer ∧ operator.wordOnly = false)
    (setterTyped : HasType
      (prepared.route.leafType :: prepared.route.leafType :: prepared.optionalLeaf :: (SourceCoreCalls.packArguments codes).type ::
        OptionalCell.referenceType prepared.route.rootType :: (SourceCoreLocalCell.coreContext scope ++ administrativeContext))
      (.apply (setter prepared (SourceCoreCalls.packArguments codes).type) (.pair (.loadCell (.var 4)) (.pair (.var 3) (.var 0))))
      (LanguageResult.resultType prepared.route.rootType) checked.catalog.definitions)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {coreEnvironment : Environment}
    {before targetHeap rhsHeap after : Dynamic.Heap} {store : Store} {sourceTarget : Dynamic.ResolvedPlace} {index : Nat}
    {right updatedRoot : Dynamic.Value}
    (environments : DataHeap.EnvRepresents checked.catalog mapping world administrativeContext scope environment coreEnvironment)
    (heaps : GenericHeap.HeapRepresents (payloadModel checked.catalog signatures functions) mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootType : sourceTarget.rootType = prepared.route.rootSourceType)
    (resolve : Dynamic.SourcePlaceResolves program context evidence source environment before place sourceTarget targetHeap)
    (evaluate : Dynamic.ExpressionEvaluates program context evidence source environment targetHeap rhs right rhsHeap)
    (written : Dynamic.ResolvedPlaceWrites
      (fun _ updated => Dynamic.AssignmentValueApplies operator sourceTarget.selected right updated)
      rhsHeap sourceTarget updatedRoot after)
    (invalidOperand : Word)
    {nextId : ExpressionId} {next : SourceCoreBasic.LoweredExpr} {nextNode : ExpressionNode}
    (nextGenerated : certificate scope nextId next) (nextFound : source.lookupExpression? nextId = some nextNode)
    {outcome : Dynamic.ExpressionOutcome} {finalHeap : Dynamic.Heap}
    (nextTrace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment after nextId outcome finalHeap) :
    ∃ value finalStore finalMap finalWorld,
      Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies operator)
        environment before place rhs updatedRoot after ∧
      Evaluates coreEnvironment store
        (execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression next.expression next.type
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalidOperand) value finalStore ∧
      ResultRepresents (payloadModel checked.catalog signatures functions) finalMap finalWorld nextNode.type next.type faults outcome value ∧
      GenericHeap.HeapRepresents (payloadModel checked.catalog signatures functions) finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before finalHeap := by
  obtain ⟨_, prefixStore, prefixMap, prefixWorld, sourceAssignment, completed, _, prefixHeaps,
    prefixMaps, prefixWorlds, prefixFrame, prefixMetadata⟩ :=
    DataPlaceAssignmentSuccess.preserves layout meaning observations faithful layouts rhsGenerated found rhsSourceType rhsCoreType
      operatorProfile setterTyped environments heaps locals slot rootType resolve evaluate written invalidOperand
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    preserves meaning nextGenerated nextFound completed (environments.extend prefixMaps prefixWorlds)
      prefixHeaps (locals.mono prefixMetadata) nextTrace
  exact ⟨value, finalStore, finalMap, finalWorld, sourceAssignment, evaluated, represented, finalHeaps,
    prefixMaps.trans maps, prefixWorlds.trans worlds, prefixFrame.trans frame, prefixMetadata.trans metadata⟩

end Solcore.SourceSemantics.CoreLowering.DataPlaceContinuation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataPlaceContinuationReflection
/-! A universal expression IH consumes the real seven-slot continuation output
of assignment reflection. The resulting trace preserves assignment-prefix
faults and effects before a successful or faulting continuation expression. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlaceContinuationReflection
open Core Frontend Frontend.SourceInference GeneralHeap DataPayload
open GenericExpressionMeaning SourceCoreDataPlaces

/-- Independent source sequencing, expressed using the existing assignment and
expression relations. This adds no evaluator or runtime-value assumption. -/
inductive Trace (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (place : PlaceResolution) (operator : Syntax.ValueAssignOp)
    (rhs next : ExpressionId) : Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | fault {reason : Dynamic.SemanticFault} {after : Dynamic.Heap}
      (assignment : Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator rhs reason after) :
      Trace program context evidence source environment before place operator rhs next (.fault reason) after
  | sequence {updated : Dynamic.Value} {written after : Dynamic.Heap} {outcome : Dynamic.ExpressionOutcome}
      (assignment : Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies operator)
        environment before place rhs updated written)
      (continuation : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment written next outcome after) :
      Trace program context evidence source environment before place operator rhs next outcome after

/-- The assignment argument is the already proved semantic output of whole
execute reflection. The continuation's actual Core trace is extracted from it
and supplied to the universal child theorem under the exact hidden slots. -/
theorem reflects {checked : SourceCoreDataCatalog.Checked} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel checked.catalog} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {certificate : Certificate} {faults : FaultRep}
    (meaning : Reflects (payloadModel checked.catalog signatures functions) program context evidence source certificate faults)
    {scope : Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    {place : PlaceResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {coreEnvironment : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {result : Value}
    (environments : DataHeap.EnvRepresents checked.catalog mapping world administrativeContext scope environment coreEnvironment)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (assignment : DataPlaceTailReflection.Result checked signatures functions program context evidence source faults
      place operator rhs environment coreEnvironment before store mapping world lowered.expression lowered.type result finalStore) :
    ∃ outcome after finalMap finalWorld,
      Trace program context evidence source environment before place operator rhs id outcome after ∧
      ResultRepresents (payloadModel checked.catalog signatures functions) finalMap finalWorld node.type lowered.type faults outcome result ∧
      GenericHeap.HeapRepresents (payloadModel checked.catalog signatures functions) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  cases assignment with
  | fault trace resultEq tokenRep heaps maps worlds frame metadata =>
    subst result
    exact ⟨_, _, _, _, .fault trace, .fault tokenRep, heaps, maps, worlds, frame, metadata⟩
  | @committed updated writtenHeap written prefixMap prefixWorld slots trace heaps maps worlds frame metadata length continuation =>
    have sameEnvironment : ReadOnly.EnvironmentsAgree Renaming.id coreEnvironment coreEnvironment := by
      intro index value found; exact found
    obtain ⟨outcome, after, finalMap, finalWorld, sourceTrace, related, finalHeaps, finalMaps, finalWorlds, finalFrame, finalMetadata⟩ :=
      DataPlaceChildExpressions.reflects meaning generated found (environments.extend maps worlds) heaps
        (locals.mono metadata) sameEnvironment slots (by simpa only [length, Expr.rename_id] using continuation)
    exact ⟨outcome, after, finalMap, finalWorld, .sequence trace sourceTrace, related, finalHeaps,
      maps.trans finalMaps, worlds.trans finalWorlds, frame.trans finalFrame, metadata.trans finalMetadata⟩

end Solcore.SourceSemantics.CoreLowering.DataPlaceContinuationReflection
end
