import Solcore.Frontend.SourceCompilationPlan
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.SourceExecutionSize

/-!
# Accepted bodies: the functions a Source state stores

The invariant the lifting of an indirect call needs: every function value a
Source state stores is a builtin, a named function at an instantiation the
compilation plan records, with an empty dictionary, or a closure that a
predicate admits. Main declarations:
`CellAwareInvocationAcceptedStoredFunctions.Value`, `Heap`, `Kept`, `KeptValue`
and `KeptOutcome`, and the guard `FamilyIndirect`.
-/

section
/-! The functions a Source state stores. Every function value is a builtin, a
named function at an instantiation the compilation plan records, with an empty
dictionary, or a closure that a predicate admits, and no cell holds a
generalized closure (`Value`, `Heap`). A data-only heap is such a heap, and
every supported form keeps it: no nested site or supported statement makes a
closure, and a closure application's copies of its captured cells are stored
cells (`Heap.copies`). The lifting asks for it only in a mode (`Kept`), which a
body family with an indirect call sets (`FamilyIndirect`). -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedStoredFunctions
open Core Frontend SourceInference

/-- A stored value: every function a builtin, a named function at an
instantiation the plan records, with an empty dictionary, or a closure that
`closures` admits. -/
inductive Value (plan : SourceCompilationPlan.Plan) (closures : Dynamic.Closure → Prop) : Dynamic.Value → Prop where
  | unit : Value plan closures .unit
  | bool (value : Bool) : Value plan closures (.bool value)
  | word (value : Core.Word) : Value plan closures (.word value)
  | integer (value : Int) : Value plan closures (.integer value)
  | product {left right : Dynamic.Value} (first : Value plan closures left) (second : Value plan closures right) :
      Value plan closures (.product left right)
  | proxy (inner : TypeSystem.Ty) : Value plan closures (.proxy inner)
  | constructed {instantiation : DataConstructorInstantiation} {arguments : List Dynamic.Value}
      (kept : ∀ argument ∈ arguments, Value plan closures argument) :
      Value plan closures (.constructed instantiation arguments)
  | mapping {keyType valueType : TypeSystem.Ty} {entries : List (Dynamic.Value × Dynamic.Value)}
      (keys : ∀ entry ∈ entries, Value plan closures entry.1)
      (values : ∀ entry ∈ entries, Value plan closures entry.2) :
      Value plan closures (.mapping keyType valueType entries)
  | closure {function : Dynamic.Closure} (kept : closures function) : Value plan closures (.closure function)
  | global {function : Dynamic.GlobalFunction}
      (planned : ∃ key, SourceCompilationPlan.exactInstantiationKey plan function.instantiation = .ok key)
      (empty : function.evidence = []) : Value plan closures (.global function)
  | builtin (function : Dynamic.BuiltinFunction) : Value plan closures (.builtin function)
  | arrayRef (element : TypeSystem.Ty) (location : Dynamic.Location) :
      Value plan closures (.arrayRef element location)
  | arrayObject {element : TypeSystem.Ty} {elements : List Dynamic.Value}
      (kept : ∀ value ∈ elements, Value plan closures value) : Value plan closures (.arrayObject element elements)
  | arraySlice {base : Dynamic.Value} (start length : Nat) (kept : Value plan closures base) :
      Value plan closures (.arraySlice base start length)
  | memref (element : TypeSystem.Ty) (location : Dynamic.Location) (position : Nat) :
      Value plan closures (.memref element location position)

/-- A heap whose cells hold no generalized closure, and only stored values. -/
def Heap (plan : SourceCompilationPlan.Plan) (closures : Dynamic.Closure → Prop) (heap : Dynamic.Heap) : Prop :=
  ∀ cell ∈ heap.cells, cell.generalized = none ∧ ∀ value, cell.value = some value → Value plan closures value

/-- A Source with an indirect call. -/
def HasIndirect (source : TypedSource) : Prop :=
  ∃ id node, source.lookupExpression? id = some node ∧
    ∃ callee ids metadata, node.form = .call callee ids (.indirect metadata)

/-- A body family with an indirect call: in its root's Source, or in the body
of an admitted callee. -/
def FamilyIndirect (program : Program) (called : DeclarationInstantiation → Prop) (root : TypedSource) : Prop :=
  HasIndirect root ∨ ∃ instantiation bodyInstance, called instantiation ∧
    Dynamic.FunctionInstantiates program instantiation bodyInstance ∧ HasIndirect bodyInstance.source

/-- A heap that is stored in a mode. -/
def Kept (plan : SourceCompilationPlan.Plan) (closures : Dynamic.Closure → Prop) (mode : Prop) (heap : Dynamic.Heap) :
    Prop :=
  mode → Heap plan closures heap

/-- A value that is stored in a mode. -/
def KeptValue (plan : SourceCompilationPlan.Plan) (closures : Dynamic.Closure → Prop) (mode : Prop)
    (value : Dynamic.Value) : Prop :=
  mode → Value plan closures value

/-- Values that are stored in a mode. -/
def KeptValues (plan : SourceCompilationPlan.Plan) (closures : Dynamic.Closure → Prop) (mode : Prop)
    (values : List Dynamic.Value) : Prop :=
  mode → ∀ value ∈ values, Value plan closures value

/-- An evaluated place path whose keys are stored in a mode. -/
def KeptKeys (plan : SourceCompilationPlan.Plan) (closures : Dynamic.Closure → Prop) (mode : Prop)
    (projections : List Dynamic.EvaluatedProjection) : Prop :=
  mode → ∀ key, Dynamic.EvaluatedProjection.index key ∈ projections → Value plan closures key

/-- A control outcome whose returned value is stored in a mode; the other
outcomes carry no value. -/
def KeptOutcome (plan : SourceCompilationPlan.Plan) (closures : Dynamic.Closure → Prop) (mode : Prop) :
    Dynamic.ControlOutcome → Prop
  | .returned value => KeptValue plan closures mode value
  | _ => True

namespace Value
variable {plan : SourceCompilationPlan.Plan} {closures : Dynamic.Closure → Prop}

theorem empty_mapping (keyType valueType : TypeSystem.Ty) : Value plan closures (.mapping keyType valueType []) :=
  .mapping (fun _ member => nomatch member) (fun _ member => nomatch member)

/-- A canonical default is data. -/
theorem of_default {type : TypeSystem.Ty} {value : Dynamic.Value} (defaulted : Dynamic.DefaultValue type value) :
    Value plan closures value := by
  induction defaulted with
  | unit => exact .unit
  | bool => exact .bool false
  | word | fixed => exact .word _
  | integer => exact .integer 0
  | product _ _ left right => exact .product left right
  | proxy inner => exact .proxy inner
  | mapping keyType valueType => exact empty_mapping keyType valueType
  | comptime _ inner => exact inner

/-- The packed value of stored values is stored. -/
theorem of_pack {values : List Dynamic.Value} {packed : Dynamic.Value} (pack : Dynamic.ValuesPack values packed)
    (kept : ∀ value ∈ values, Value plan closures value) : Value plan closures packed := by
  induction pack with
  | nil => exact .unit
  | singleton value => exact List.forall_mem_singleton.mp kept
  | cons _ ih => exact .product (List.forall_mem_cons.mp kept).1 (ih (List.forall_mem_cons.mp kept).2)

/-- The values of a stored packed value are stored. -/
theorem of_unpack {values : List Dynamic.Value} {packed : Dynamic.Value} (pack : Dynamic.ValuesPack values packed)
    (kept : Value plan closures packed) : ∀ value ∈ values, Value plan closures value := by
  induction pack with
  | nil => exact List.forall_mem_nil _
  | singleton value => exact List.forall_mem_singleton.mpr kept
  | cons _ ih => cases kept with | product first rest => exact List.forall_mem_cons.mpr ⟨first, ih rest⟩

/-- A first-match lookup in stored entries selects a stored value. -/
theorem of_lookup {key value : Dynamic.Value} {entries : List (Dynamic.Value × Dynamic.Value)}
    (kept : ∀ entry ∈ entries, Value plan closures entry.2) (lookup : Dynamic.MappingLookup key entries value) :
    Value plan closures value := by
  induction lookup with
  | head => exact kept _ List.mem_cons_self
  | tail _ _ ih => exact ih fun entry member => kept entry (List.mem_cons_of_mem _ member)

/-- A first-match lookup in a stored mapping selects a stored value. -/
theorem of_mapping_lookup {keyType valueType : TypeSystem.Ty} {entries : List (Dynamic.Value × Dynamic.Value)}
    {key value : Dynamic.Value} (kept : Value plan closures (.mapping keyType valueType entries))
    (lookup : Dynamic.MappingLookup key entries value) : Value plan closures value := by
  cases kept with
  | mapping _ values => exact of_lookup values lookup

/-- A position of stored values selects a stored value. -/
theorem of_select {values : List Dynamic.Value} {index : Nat} {selected : Dynamic.Value}
    (kept : ∀ value ∈ values, Value plan closures value) (selectedAt : Dynamic.ValueAt values index selected) :
    Value plan closures selected := by
  induction selectedAt with
  | head => exact kept _ List.mem_cons_self
  | tail _ ih => exact ih fun value member => kept value (List.mem_cons_of_mem _ member)

/-- A replacement by a stored value in stored values gives stored values. -/
theorem of_replace {values updated : List Dynamic.Value} {index : Nat} {replacement : Dynamic.Value}
    (kept : ∀ value ∈ values, Value plan closures value) (stored : Value plan closures replacement)
    (replaced : Dynamic.ValuesReplaceAt values index replacement updated) :
    ∀ value ∈ updated, Value plan closures value := by
  induction replaced with
  | head => exact List.forall_mem_cons.mpr ⟨stored, (List.forall_mem_cons.mp kept).2⟩
  | tail _ ih =>
    exact List.forall_mem_cons.mpr ⟨(List.forall_mem_cons.mp kept).1, ih (List.forall_mem_cons.mp kept).2 stored⟩

private theorem insert_origin {key value : Dynamic.Value} {entries updated : List (Dynamic.Value × Dynamic.Value)}
    (inserted : Dynamic.MappingInsert key value entries updated) :
    ∀ entry ∈ updated, entry ∈ entries ∨ entry = (key, value) := by
  cases inserted with
  | update replacement => induction replacement <;> grind
  | append => grind

/-- An insertion of a stored entry into a stored mapping gives a stored mapping. -/
theorem of_insert {keyType valueType : TypeSystem.Ty} {key value : Dynamic.Value}
    {entries updated : List (Dynamic.Value × Dynamic.Value)}
    (kept : Value plan closures (.mapping keyType valueType entries)) (storedKey : Value plan closures key)
    (storedValue : Value plan closures value) (inserted : Dynamic.MappingInsert key value entries updated) :
    Value plan closures (.mapping keyType valueType updated) := by
  cases kept with
  | mapping keys values =>
    refine .mapping (fun entry member => ?_) (fun entry member => ?_) <;>
      rcases insert_origin inserted entry member with old | rfl
    all_goals first | exact keys _ old | exact values _ old | assumption

/-- An update through an evaluated path with stored keys from a stored value,
whose leaf modification gives stored values, gives a stored value. -/
theorem of_update {Modify : Option Dynamic.Value → Dynamic.Value → Prop} {initial : Option Dynamic.Value}
    {projections : List Dynamic.EvaluatedProjection} {updated : Dynamic.Value}
    (rebuilt : Dynamic.ProjectionsUpdate Modify initial projections updated)
    (kept : ∀ value, initial = some value → Value plan closures value)
    (keys : ∀ key, Dynamic.EvaluatedProjection.index key ∈ projections → Value plan closures key)
    (modify : ∀ current updated, Modify current updated → Value plan closures updated) :
    Value plan closures updated := by
  induction rebuilt with
  | leaf modified => exact modify _ _ modified
  | indexFound lookup _ inserted ih =>
    have child := ih (fun _ same => by cases same; exact of_mapping_lookup (kept _ rfl) lookup)
      (fun key member => keys key (List.mem_cons_of_mem _ member))
    exact of_insert (kept _ rfl) (keys _ List.mem_cons_self) child inserted
  | indexDefault _ defaulted _ inserted ih =>
    have child := ih (fun _ same => by cases same; exact of_default defaulted)
      (fun key member => keys key (List.mem_cons_of_mem _ member))
    exact of_insert (kept _ rfl) (keys _ List.mem_cons_self) child inserted
  | member selectedAt _ replaced ih =>
    cases kept _ rfl with
    | constructed arguments =>
      have child := ih (fun value same => by cases same; exact of_select arguments selectedAt)
        (fun key member => keys key (List.mem_cons_of_mem _ member))
      exact .constructed (of_replace arguments child replaced)
  | element selectedAt _ replaced ih =>
    cases kept _ rfl with
    | arrayObject elements =>
      have child := ih (fun value same => by cases same; exact of_select elements selectedAt)
        (fun key member => keys key (List.mem_cons_of_mem _ member))
      exact .arrayObject (of_replace elements child replaced)

/-- A unary operator's result is data. -/
theorem of_unary {operandType : Option TypeSystem.Ty} {operator : Syntax.UnaryOp} {input output : Dynamic.Value}
    (applies : Dynamic.UnaryValueApplies operandType operator input output) : Value plan closures output := by
  cases applies with
  | primitive _ applies | fixed _ applies => cases applies <;> constructor

/-- A binary operator's result is data. -/
theorem of_binary {operandType : Option TypeSystem.Ty} {operator : Syntax.BinaryOp} {left right output : Dynamic.Value}
    (applies : Dynamic.BinaryValueApplies operandType operator left right output) : Value plan closures output := by
  cases applies with
  | primitive _ applies | fixed _ applies => cases applies <;> constructor

/-- A short-circuited result is data. -/
theorem of_short {operator : Syntax.BinaryOp} {left result : Dynamic.Value}
    (circuit : Dynamic.ShortCircuits operator left result) : Value plan closures result := by
  cases circuit <;> constructor

/-- A builtin's result is data. -/
theorem of_builtin {function : BuiltinFunctionId} {arguments : List Dynamic.Value} {result : Dynamic.Value}
    (applies : Dynamic.BuiltinApplies function arguments result) : Value plan closures result := by
  cases applies with
  | wordOpcode applies =>
    obtain ⟨_, _, _, _, _, rfl⟩ := Dynamic.wordOpcodeValue_inv applies
    constructor
  | _ => constructor

/-- A literal's value is data. -/
theorem of_literal {literal : Syntax.CoreLiteralValue} {value : Dynamic.Value}
    (constructs : Dynamic.LiteralConstructs literal value) : Value plan closures value := by
  cases constructs
  constructor

/-- A resolved integer literal's value is data. -/
theorem of_integer_literal {context : SourceSemantics.Context} {literal : Syntax.CoreLiteralValue}
    {resolution : IntegerLiteralResolution} {value : Dynamic.Value}
    (constructs : Dynamic.ResolvedIntegerLiteralConstructs context literal resolution value) :
    Value plan closures value := by
  cases constructs <;> constructor

/-- A compound assignment of a stored value gives that value or data. -/
theorem of_compound {type : TypeSystem.Ty} {operator : Syntax.ValueAssignOp} {current : Option Dynamic.Value}
    {right result : Dynamic.Value} (applies : Dynamic.CompoundAssignmentApplies type operator current right result)
    (stored : Value plan closures right) : Value plan closures result := by
  cases applies with
  | primitive _ applies =>
    cases applies with
    | equal => exact stored
    | _ => rename_i applies; cases applies <;> constructor
  | _ => rename_i applies; cases applies <;> constructor

/-- An in-place `~` gives data. -/
theorem of_bitNot {targetType : TypeSystem.Ty} {current : Option Dynamic.Value} {result : Dynamic.Value}
    (applies : Dynamic.BitNotAssignmentApplies targetType current result) : Value plan closures result := by
  cases applies with
  | primitive _ applies | narrow _ applies => cases applies <;> constructor

/-- The values a pattern binds from stored values are stored. -/
theorem of_matches {context : SourceSemantics.Context} :
    (∀ {value : Dynamic.Value} {instructions rest : List MatchPatternInstruction}
      {bindings : List (TypedBinder × Dynamic.Value)},
      Dynamic.PatternInstructionMatches context value instructions bindings rest → Value plan closures value →
        ∀ binding ∈ bindings, Value plan closures binding.2) := by
  intro value instructions rest bindings matched
  refine Dynamic.PatternInstructionMatches.rec
    (motive_1 := fun value _ bindings _ _ =>
      Value plan closures value → ∀ binding ∈ bindings, Value plan closures binding.2)
    (motive_2 := fun values _ bindings _ _ =>
      (∀ value ∈ values, Value plan closures value) → ∀ binding ∈ bindings, Value plan closures binding.2)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ matched
  · intro _ _ _ _ member; nomatch member
  · intro _ _ _ _ _ _ _ member; nomatch member
  · intro value _ _ kept binding member
    rw [List.mem_singleton.mp member]
    exact kept
  · intro _ _ _ _ _ _ _ _ _ _ children kept
    cases kept with
    | constructed arguments => exact children arguments
  · intro _ _ _ _ _ _ packed _ _ children kept
    exact children (of_unpack packed kept)
  · intro _ _ _ _ _ children _
    exact children fun _ member => by rw [List.mem_singleton.mp member]; exact .word _
  · intro _ _ _ _ member; nomatch member
  · intro _ _ _ member; nomatch member
  · intro _ _ _ _ _ _ _ _ _ head tail kept binding member
    rcases List.mem_append.mp member with first | second
    · exact head (kept _ List.mem_cons_self) binding first
    · exact tail (fun value member => kept value (List.mem_cons_of_mem _ member)) binding second

/-- The values a selected match arm binds from a stored scrutinee are stored. -/
theorem of_arm {context : SourceSemantics.Context} {value : Dynamic.Value} {arms : List TypedMatchCase}
    {fallback : Option (List StatementId)} {body : List StatementId} {bindings : List (TypedBinder × Dynamic.Value)}
    (select : Dynamic.MatchCasesSelect context value arms fallback (.arm body bindings))
    (kept : Value plan closures value) : ∀ bound ∈ bindings.map Prod.snd, Value plan closures bound := by
  intro bound member
  obtain ⟨binding, inBindings, rfl⟩ := List.mem_map.mp member
  generalize selection : Dynamic.MatchCaseSelection.arm body bindings = selected at select
  induction select with
  | head matched =>
    cases selection
    cases matched with
    | intro _ matched => exact of_matches matched kept binding inBindings
  | tail _ _ ih => exact ih selection
  | default => cases selection
  | noBranch => cases selection

end Value

namespace Heap
variable {plan : SourceCompilationPlan.Plan} {closures : Dynamic.Closure → Prop}

private theorem cell_mem {cells : List Dynamic.Cell} {index : Nat} {cell : Dynamic.Cell}
    (selected : Dynamic.Heap.CellAt cells index cell) : cell ∈ cells := by
  induction selected <;> grind

/-- A cell of a stored heap is ordinary and holds a stored value. -/
theorem read {heap : Dynamic.Heap} {location : Dynamic.Location} {cell : Dynamic.Cell} (kept : Heap plan closures heap)
    (read : Dynamic.Heap.Reads heap location cell) :
    cell.generalized = none ∧ ∀ value, cell.value = some value → Value plan closures value := by
  cases read with
  | intro selected => exact kept cell (cell_mem selected)

/-- The empty heap is stored. -/
theorem empty : Heap plan closures ⟨[]⟩ := fun _ member => nomatch member

/-- A stored heap with one more ordinary cell, holding a stored value or none,
is stored. -/
theorem push {heap : Dynamic.Heap} {type : TypeSystem.Ty} {initial : Option Dynamic.Value}
    (kept : Heap plan closures heap) (stored : ∀ value, initial = some value → Value plan closures value) :
    Heap plan closures ⟨heap.cells ++ [{ type := type, value := initial }]⟩ := by
  intro cell member
  rcases List.mem_append.mp member with old | new
  · exact kept cell old
  · obtain rfl := List.mem_singleton.mp new
    exact ⟨rfl, stored⟩

/-- An allocation of a stored value or none keeps a stored heap. -/
theorem allocates {heap after : Dynamic.Heap} {type : TypeSystem.Ty} {initial : Option Dynamic.Value}
    {location : Dynamic.Location} (kept : Heap plan closures heap)
    (stored : ∀ value, initial = some value → Value plan closures value)
    (allocation : Dynamic.Heap.Allocates heap type initial location after) : Heap plan closures after := by
  cases allocation
  exact kept.push stored

private theorem write_origin {cells updated : List Dynamic.Cell} {index : Nat} {replacement : Dynamic.Cell}
    (write : Dynamic.Heap.CellsWrite cells index replacement updated) :
    ∀ cell ∈ updated, cell ∈ cells ∨ cell = replacement := by
  induction write <;> grind

/-- A write of a stored value or none keeps a stored heap. -/
theorem writes {heap after : Dynamic.Heap} {location : Dynamic.Location} {value : Option Dynamic.Value}
    (kept : Heap plan closures heap) (stored : ∀ written, value = some written → Value plan closures written)
    (write : Dynamic.Heap.Writes heap location value after) : Heap plan closures after := by
  cases write with
  | intro read cells =>
    have previous := kept.read read
    intro cell member
    rcases write_origin cells cell member with old | rfl
    · exact kept cell old
    · exact ⟨previous.1, stored⟩

/-- An allocation of stored binder values keeps a stored heap. -/
theorem allocates_binders {environment final : Dynamic.Environment} {heap after : Dynamic.Heap}
    {binders : List TypedBinder} {values : List Dynamic.Value} (kept : Heap plan closures heap)
    (stored : ∀ value ∈ values, Value plan closures value)
    (allocate : Dynamic.BindersAllocate environment heap binders values final after) : Heap plan closures after := by
  induction allocate with
  | nil => exact kept
  | cons allocation _ ih =>
    exact ih (kept.allocates (fun _ same => by cases same; exact stored _ List.mem_cons_self) allocation)
      (fun value member => stored value (List.mem_cons_of_mem _ member))

/-- A new array's default element is data, and its allocation keeps a stored heap. -/
theorem new_array_default {heap after : Dynamic.Heap} {element : TypeSystem.Ty} {zero : Dynamic.Value}
    (kept : Heap plan closures heap) (default : Dynamic.NewArrayDefault heap element zero after) :
    Heap plan closures after ∧ Value plan closures zero := by
  cases default with
  | word | fixed => exact ⟨kept, .word _⟩
  | array allocates =>
    exact ⟨kept.allocates (fun _ same => by cases same; exact .arrayObject fun _ member => nomatch member) allocates,
      .arrayRef _ _⟩

/-- An element read through a view of a stored heap is stored. -/
theorem view_reads {heap : Dynamic.Heap} {view value : Dynamic.Value} {position : Nat} (kept : Heap plan closures heap)
    (reads : Dynamic.ViewReads heap view position value) : Value plan closures value := by
  induction reads with
  | array read stored elementAt =>
    cases (kept.read read).2 _ stored with
    | arrayObject elements => exact elements _ (List.mem_of_getElem? elementAt)
  | slice _ _ ih => exact ih

/-- The elements copied through a view of a stored heap are stored. -/
theorem view_copies {heap : Dynamic.Heap} {view : Dynamic.Value} {position count : Nat} {values : List Dynamic.Value}
    (kept : Heap plan closures heap) (copies : Dynamic.ViewCopies heap view position count values) :
    ∀ value ∈ values, Value plan closures value := by
  induction copies with
  | nil => exact List.forall_mem_nil _
  | cons reads _ ih => exact List.forall_mem_cons.mpr ⟨kept.view_reads reads, ih⟩

private theorem initial_value {cell : Dynamic.Cell} {initial : Option Dynamic.Value}
    (stored : ∀ value, cell.value = some value → Value plan closures value)
    (initialValue : Dynamic.RootInitialValue cell initial) :
    ∀ value, initial = some value → Value plan closures value := by
  cases initialValue with
  | initialized => exact stored
  | emptyMapping => intro _ same; cases same; exact Value.empty_mapping _ _
  | uninitialized => intro _ same; cases same

/-- A place write through stored keys, whose leaf modification gives stored
values, keeps a stored heap. -/
theorem place_writes {Modify : Option Dynamic.Value → Dynamic.Value → Prop} {heap after : Dynamic.Heap}
    {place : Dynamic.ResolvedPlace} {updatedRoot : Dynamic.Value} (kept : Heap plan closures heap)
    (keys : ∀ key, Dynamic.EvaluatedProjection.index key ∈ place.projections → Value plan closures key)
    (modify : ∀ current updated, Modify current updated → Value plan closures updated)
    (write : Dynamic.ResolvedPlaceWrites Modify heap place updatedRoot after) : Heap plan closures after := by
  cases write with
  | intro currentRead _ initialValue rebuilt written =>
    have start := initial_value (kept.read currentRead).2 initialValue
    exact kept.writes (fun _ same => by cases same; exact Value.of_update rebuilt start keys modify) written

/-- Copying captured bindings from a stored heap adds copies of its cells, which
keeps a stored heap. -/
theorem copies {source : TypedSource} {environment copied : Dynamic.Environment} {heap after : Dynamic.Heap}
    (kept : Heap plan closures heap) (copy : Dynamic.EnvironmentCopies source environment heap copied after) :
    Heap plan closures after := by
  induction copy with
  | nil => exact kept
  | shared _ _ ih => exact ih kept
  | copied _ read allocate _ ih =>
    cases allocate
    refine ih fun other member => ?_
    rcases List.mem_append.mp member with old | new
    · exact kept other old
    · obtain rfl := List.mem_singleton.mp new
      exact kept.read read

end Heap

/-- Restoring a control outcome to its entry bindings keeps its returned value. -/
theorem KeptOutcome.restore {plan : SourceCompilationPlan.Plan} {closures : Dynamic.Closure → Prop} {mode : Prop}
    {environment : Dynamic.Environment} {outcome : Dynamic.ControlOutcome}
    (kept : KeptOutcome plan closures mode outcome) :
    KeptOutcome plan closures mode (Dynamic.restoreControl environment outcome) := by
  cases outcome <;> first | exact kept | trivial

namespace Kept
variable {plan : SourceCompilationPlan.Plan} {closures : Dynamic.Closure → Prop} {mode : Prop}
  {heap after : Dynamic.Heap}

/-- A stored heap with one more ordinary cell holding a stored value is stored. -/
theorem allocates {type : TypeSystem.Ty} {value : Dynamic.Value} {location : Dynamic.Location}
    (kept : Kept plan closures mode heap) (stored : KeptValue plan closures mode value)
    (allocation : Dynamic.Heap.Allocates heap type (some value) location after) : Kept plan closures mode after :=
  fun active => (kept active).allocates (fun _ same => by cases same; exact stored active) allocation

/-- A stored heap with one more empty ordinary cell is stored. -/
theorem allocates_none {type : TypeSystem.Ty} {location : Dynamic.Location} (kept : Kept plan closures mode heap)
    (allocation : Dynamic.Heap.Allocates heap type none location after) : Kept plan closures mode after :=
  fun active => (kept active).allocates (fun _ same => by cases same) allocation

/-- Copying captured bindings keeps a stored heap. -/
theorem copies {source : TypedSource} {environment copied : Dynamic.Environment} (kept : Kept plan closures mode heap)
    (copy : Dynamic.EnvironmentCopies source environment heap copied after) : Kept plan closures mode after :=
  fun active => (kept active).copies copy

/-- A write of a stored value keeps a stored heap. -/
theorem writes {location : Dynamic.Location} {value : Dynamic.Value} (kept : Kept plan closures mode heap)
    (stored : KeptValue plan closures mode value) (write : Dynamic.Heap.Writes heap location (some value) after) :
    Kept plan closures mode after :=
  fun active => (kept active).writes (fun _ same => by cases same; exact stored active) write

/-- An allocation of stored binder values keeps a stored heap. -/
theorem binders {environment final : Dynamic.Environment} {binders : List TypedBinder}
    {values : List Dynamic.Value} (kept : Kept plan closures mode heap) (stored : KeptValues plan closures mode values)
    (allocate : Dynamic.BindersAllocate environment heap binders values final after) : Kept plan closures mode after :=
  fun active => (kept active).allocates_binders (stored active) allocate

/-- A place write through stored keys, whose leaf modification gives stored
values, keeps a stored heap. -/
theorem place_writes {Modify : Option Dynamic.Value → Dynamic.Value → Prop} {place : Dynamic.ResolvedPlace}
    {updatedRoot : Dynamic.Value} (kept : Kept plan closures mode heap)
    (keys : KeptKeys plan closures mode place.projections)
    (modify : mode → ∀ current updated, Modify current updated → Value plan closures updated)
    (write : Dynamic.ResolvedPlaceWrites Modify heap place updatedRoot after) : Kept plan closures mode after :=
  fun active => (kept active).place_writes (keys active) (modify active) write

/-- A new array of a default element, allocated after the default, keeps a
stored heap. -/
theorem new_array {element : TypeSystem.Ty} {zero : Dynamic.Value} {defaulted : Dynamic.Heap} {count : Nat}
    {location : Dynamic.Location} (kept : Kept plan closures mode heap)
    (default : Dynamic.NewArrayDefault heap element zero defaulted)
    (allocates : Dynamic.Heap.Allocates defaulted (TypeSystem.Ty.arrayObject element)
      (some (.arrayObject element (List.replicate count zero))) location after) : Kept plan closures mode after :=
  fun active => by
    obtain ⟨defaultKept, zeroKept⟩ := (kept active).new_array_default default
    exact defaultKept.allocates (fun _ same => by
      cases same
      exact .arrayObject fun _ member => by rw [List.eq_of_mem_replicate member]; exact zeroKept) allocates

/-- A store of a stored value at an element of an array's cell keeps a stored
heap. -/
theorem stores {location : Dynamic.Location} {cell : Dynamic.Cell} {element : TypeSystem.Ty}
    {elements updated : List Dynamic.Value} {position : Nat} {stored : Dynamic.Value}
    (kept : Kept plan closures mode heap) (storedKept : KeptValue plan closures mode stored)
    (read : Dynamic.Heap.Reads heap location cell)
    (current : cell.value = some (.arrayObject element elements))
    (replace : Dynamic.ValuesReplaceAt elements position stored updated)
    (write : Dynamic.Heap.Writes heap location (some (.arrayObject element updated)) after) :
    Kept plan closures mode after :=
  kept.writes (fun active => by
    cases ((kept active).read read).2 _ current with
    | arrayObject elements => exact .arrayObject (Value.of_replace elements (storedKept active) replace)) write

/-- An assignment's write of a stored value through stored keys keeps a stored
heap. -/
theorem assigns {targetType : TypeSystem.Ty} {operator : Syntax.ValueAssignOp} {selected : Option Dynamic.Value}
    {right : Dynamic.Value} {place : Dynamic.ResolvedPlace} {updatedRoot : Dynamic.Value}
    (kept : Kept plan closures mode heap) (keys : KeptKeys plan closures mode place.projections)
    (stored : KeptValue plan closures mode right)
    (write : Dynamic.ResolvedPlaceWrites
      (fun _ updated => Dynamic.CompoundAssignmentApplies targetType operator selected right updated) heap place
      updatedRoot after) : Kept plan closures mode after :=
  kept.place_writes keys (fun active _ _ applies => Value.of_compound applies (stored active)) write

/-- An in-place `~`'s write through stored keys keeps a stored heap. -/
theorem bitNots {targetType : TypeSystem.Ty} {selected : Option Dynamic.Value} {place : Dynamic.ResolvedPlace}
    {updatedRoot : Dynamic.Value} (kept : Kept plan closures mode heap)
    (keys : KeptKeys plan closures mode place.projections)
    (write : Dynamic.ResolvedPlaceWrites (fun _ updated => Dynamic.BitNotAssignmentApplies targetType selected updated)
      heap place updatedRoot after) : Kept plan closures mode after :=
  kept.place_writes keys (fun _ _ _ applies => Value.of_bitNot applies) write

end Kept

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedStoredFunctions
end
