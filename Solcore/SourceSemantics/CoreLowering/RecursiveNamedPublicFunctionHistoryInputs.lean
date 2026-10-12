import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDataArgumentReceipts
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicFunctionHistoryEntries

/-! Public input descriptions retain literal members of a finite function
history. Distinct handles and repeated aliases can occur beside data at any
finite depth. Raw constructor and mapping metadata, counts and entry order
are preserved without assuming native representation or execution. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicFunctionHistoryInputs
open Core Frontend SourceInference
open SourceCoreIndexedSession
open RecursiveNamedPublicFunctionHistory (Entry)

mutual
  inductive Input (history : List Entry) (context : SourceSemantics.Context) :
      TypeSystem.Ty → SourceCorePublicValues.Value → Dynamic.Value → Prop where
    | retained (entry : Entry) (member : entry ∈ history) :
        Input history context entry.sourceType (.function entry.handle) entry.source
    | data {type : TypeSystem.Ty} {value : SourceCorePublicValues.Value} {source : Dynamic.Value}
        (typed : RecursiveNamedPublicDataArgumentReceipts.PublicDataTyped context value type)
        (meaning : RecursiveNamedPublicDataInputs.Means value source) :
        Input history context type value source
    | product {leftType rightType : TypeSystem.Ty}
        {left right : SourceCorePublicValues.Value} {first second : Dynamic.Value}
        (leftInput : Input history context leftType left first)
        (rightInput : Input history context rightType right second) :
        Input history context (.product leftType rightType) (.product left right) (.product first second)
    | constructed {metadata : DataConstructorInstantiation}
        {values : List SourceCorePublicValues.Value} {sources : List Dynamic.Value}
        (valid : DataConstructorInstantiation.Valid context metadata)
        (payloads : Inputs history context metadata.payloadTypes values sources) :
        Input history context metadata.resultType (.constructed metadata values) (.constructed metadata sources)
    | mapping {key value : TypeSystem.Ty}
        {entries : List (SourceCorePublicValues.Value × SourceCorePublicValues.Value)}
        {sources : List (Dynamic.Value × Dynamic.Value)}
        (stored : Entries history context key value entries sources) :
        Input history context (.mapping key value) (.mapping key value entries) (.mapping key value sources)
    | comptime {type : TypeSystem.Ty} {value : SourceCorePublicValues.Value} {source : Dynamic.Value}
        (input : Input history context type value source) :
        Input history context (.comptime type) value source

  inductive Inputs (history : List Entry) (context : SourceSemantics.Context) :
      List TypeSystem.Ty → List SourceCorePublicValues.Value → List Dynamic.Value → Prop where
    | nil : Inputs history context [] [] []
    | cons {type : TypeSystem.Ty} {types : List TypeSystem.Ty}
        {value : SourceCorePublicValues.Value} {values : List SourceCorePublicValues.Value}
        {source : Dynamic.Value} {sources : List Dynamic.Value}
        (head : Input history context type value source)
        (tail : Inputs history context types values sources) :
        Inputs history context (type :: types) (value :: values) (source :: sources)

  inductive Entries (history : List Entry) (context : SourceSemantics.Context) : TypeSystem.Ty → TypeSystem.Ty →
      List (SourceCorePublicValues.Value × SourceCorePublicValues.Value) →
      List (Dynamic.Value × Dynamic.Value) → Prop where
    | empty (key value : TypeSystem.Ty) : Entries history context key value [] []
    | entry {key value : TypeSystem.Ty}
        {first second : SourceCorePublicValues.Value} {left right : Dynamic.Value}
        {rest : List (SourceCorePublicValues.Value × SourceCorePublicValues.Value)}
        {sources : List (Dynamic.Value × Dynamic.Value)}
        (keyInput : Input history context key first left)
        (valueInput : Input history context value second right)
        (remaining : Entries history context key value rest sources) :
        Entries history context key value ((first, second) :: rest) ((left, right) :: sources)
end

variable {history : List Entry} {context : SourceSemantics.Context}

theorem Input.source_hasType {type : TypeSystem.Ty} {value : SourceCorePublicValues.Value}
    {source : Dynamic.Value} (receipt : Input history context type value source)
    {heap : Dynamic.Heap}
    (retainedTyped : ∀ entry, entry ∈ history →
      Dynamic.ValueHasType context heap entry.source entry.sourceType) :
    Dynamic.ValueHasType context heap source type := by
  induction receipt using Input.rec
    (motive_2 := fun types _ sources _ => Dynamic.ValuesHaveTypes context heap sources types)
    (motive_3 := fun key value _ sources _ => Dynamic.MappingEntriesHaveTypes context heap sources key value) with
  | retained entry member => exact retainedTyped entry member
  | data typed meaning => exact RecursiveNamedPublicDataArgumentReceipts.PublicDataTyped.source_hasType typed meaning
  | product _ _ left right => exact .product left right
  | constructed valid _ payloads => exact .constructed valid payloads
  | mapping _ entries => exact .mapping entries
  | comptime _ typed => exact .comptime typed
  | nil => exact .nil
  | cons _ _ head tail => exact .cons head tail
  | empty key value => exact .nil key value
  | entry _ _ _ key value rest => exact .cons key value rest

theorem Inputs.source_hasTypes {types : List TypeSystem.Ty}
    {values : List SourceCorePublicValues.Value} {sources : List Dynamic.Value}
    (receipts : Inputs history context types values sources)
    {heap : Dynamic.Heap}
    (retainedTyped : ∀ entry, entry ∈ history →
      Dynamic.ValueHasType context heap entry.source entry.sourceType) :
    Dynamic.ValuesHaveTypes context heap sources types := by
  induction types generalizing values sources with
  | nil => cases receipts; exact .nil
  | cons type types ih => cases receipts with
    | cons head tail => exact .cons (head.source_hasType retainedTyped) (ih tail)

theorem Inputs.source_length {types : List TypeSystem.Ty}
    {values : List SourceCorePublicValues.Value} {sources : List Dynamic.Value}
    (receipts : Inputs history context types values sources) : sources.length = types.length := by
  induction types generalizing values sources with
  | nil => cases receipts; rfl
  | cons type types ih => cases receipts with
    | cons _ tail => exact congrArg Nat.succ (ih tail)

theorem Inputs.lookup {types : List TypeSystem.Ty}
    {values : List SourceCorePublicValues.Value} {sources : List Dynamic.Value}
    (receipts : Inputs history context types values sources)
    {index : Nat} {type : TypeSystem.Ty} (found : types[index]? = some type) :
    ∃ value source, values[index]? = some value ∧ sources[index]? = some source ∧
      Input history context type value source := by
  induction types generalizing values sources index with
  | nil => simp at found
  | cons type types ih => cases receipts with
    | cons head tail =>
      cases index with
      | zero =>
          have same := Option.some.inj found
          cases same
          exact ⟨_, _, rfl, rfl, head⟩
      | succ index =>
          obtain ⟨value, source, valueAt, sourceAt, receipt⟩ := ih tail found
          exact ⟨value, source, valueAt, sourceAt, receipt⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicFunctionHistoryInputs
