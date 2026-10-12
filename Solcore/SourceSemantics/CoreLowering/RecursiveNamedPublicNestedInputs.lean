import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicMixedArgumentReceipts

/-! Independent public input descriptions retain raw types and the Source
value at every nested position. Function leaves use genuine issuance and
inventory receipts. Containers preserve payload and mapping entry order;
none of these constructors assumes a native representation or execution law. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicNestedInputs
open Core Frontend SourceInference
open SourceCoreIndexedSession
open CallableIndexedOwnedPreparedFiniteNamedInventories (Inventory)

mutual
  inductive Input {compiled : SourceCoreUnifiedCompilation.Compiled}
      {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
      (rows : Inventory inputs) {artifact : Artifact} (session : Session artifact)
      (context : SourceSemantics.Context) :
      TypeSystem.Ty → SourceCorePublicValues.Value → Dynamic.Value → Prop where
    | leaf {type : TypeSystem.Ty} {value : SourceCorePublicValues.Value} {source : Dynamic.Value}
        (receipt : RecursiveNamedPublicMixedArgumentReceipts.Input rows session context type value source) :
        Input rows session context type value source
    | product {leftType rightType : TypeSystem.Ty}
        {left right : SourceCorePublicValues.Value} {first second : Dynamic.Value}
        (leftInput : Input rows session context leftType left first)
        (rightInput : Input rows session context rightType right second) :
        Input rows session context (.product leftType rightType) (.product left right) (.product first second)
    | constructed {metadata : DataConstructorInstantiation}
        {values : List SourceCorePublicValues.Value} {sources : List Dynamic.Value}
        (valid : DataConstructorInstantiation.Valid context metadata)
        (payloads : Inputs rows session context metadata.payloadTypes values sources) :
        Input rows session context metadata.resultType (.constructed metadata values) (.constructed metadata sources)
    | mapping {key value : TypeSystem.Ty}
        {entries : List (SourceCorePublicValues.Value × SourceCorePublicValues.Value)}
        {sources : List (Dynamic.Value × Dynamic.Value)}
        (stored : Entries rows session context key value entries sources) :
        Input rows session context (.mapping key value) (.mapping key value entries) (.mapping key value sources)
    | comptime {type : TypeSystem.Ty} {value : SourceCorePublicValues.Value} {source : Dynamic.Value}
        (input : Input rows session context type value source) :
        Input rows session context (.comptime type) value source

  inductive Inputs {compiled : SourceCoreUnifiedCompilation.Compiled}
      {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
      (rows : Inventory inputs) {artifact : Artifact} (session : Session artifact)
      (context : SourceSemantics.Context) :
      List TypeSystem.Ty → List SourceCorePublicValues.Value → List Dynamic.Value → Prop where
    | nil : Inputs rows session context [] [] []
    | cons {type : TypeSystem.Ty} {types : List TypeSystem.Ty}
        {value : SourceCorePublicValues.Value} {values : List SourceCorePublicValues.Value}
        {source : Dynamic.Value} {sources : List Dynamic.Value}
        (head : Input rows session context type value source)
        (tail : Inputs rows session context types values sources) :
        Inputs rows session context (type :: types) (value :: values) (source :: sources)

  inductive Entries {compiled : SourceCoreUnifiedCompilation.Compiled}
      {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
      (rows : Inventory inputs) {artifact : Artifact} (session : Session artifact)
      (context : SourceSemantics.Context) : TypeSystem.Ty → TypeSystem.Ty →
      List (SourceCorePublicValues.Value × SourceCorePublicValues.Value) →
      List (Dynamic.Value × Dynamic.Value) → Prop where
    | empty (key value : TypeSystem.Ty) : Entries rows session context key value [] []
    | entry {key value : TypeSystem.Ty}
        {first second : SourceCorePublicValues.Value} {left right : Dynamic.Value}
        {rest : List (SourceCorePublicValues.Value × SourceCorePublicValues.Value)}
        {sources : List (Dynamic.Value × Dynamic.Value)}
        (keyInput : Input rows session context key first left)
        (valueInput : Input rows session context value second right)
        (remaining : Entries rows session context key value rest sources) :
        Entries rows session context key value ((first, second) :: rest) ((left, right) :: sources)
end

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
  {rows : Inventory inputs} {artifact : Artifact} {session : Session artifact}
  {context : SourceSemantics.Context}

theorem Input.source_hasType {type : TypeSystem.Ty} {value : SourceCorePublicValues.Value}
    {source : Dynamic.Value} (receipt : Input rows session context type value source)
    {heap : Dynamic.Heap}
    (leaves : ∀ {type value source},
      RecursiveNamedPublicMixedArgumentReceipts.Input rows session context type value source →
      Dynamic.ValueHasType context heap source type) : Dynamic.ValueHasType context heap source type := by
  induction receipt using Input.rec
    (motive_2 := fun types _ sources _ => Dynamic.ValuesHaveTypes context heap sources types)
    (motive_3 := fun key value _ sources _ => Dynamic.MappingEntriesHaveTypes context heap sources key value) with
  | leaf receipt => exact leaves receipt
  | product _ _ left right => exact .product left right
  | constructed valid _ payloads => exact .constructed valid payloads
  | mapping _ entries => exact .mapping entries
  | comptime _ typed => exact .comptime typed
  | nil => exact .nil
  | cons _ _ head tail => exact .cons head tail
  | empty key value => exact .nil key value
  | entry _ _ _ key value rest => exact .cons key value rest

theorem Inputs.source_length {types : List TypeSystem.Ty}
    {values : List SourceCorePublicValues.Value} {sources : List Dynamic.Value}
    (receipts : Inputs rows session context types values sources) : sources.length = types.length := by
  induction types generalizing values sources with
  | nil => cases receipts; rfl
  | cons type types ih => cases receipts with
    | cons _ tail => exact congrArg Nat.succ (ih tail)

theorem Inputs.lookup {types : List TypeSystem.Ty}
    {values : List SourceCorePublicValues.Value} {sources : List Dynamic.Value}
    (receipts : Inputs rows session context types values sources)
    {index : Nat} {type : TypeSystem.Ty} (found : types[index]? = some type) :
    ∃ value source, values[index]? = some value ∧ sources[index]? = some source ∧
      Input rows session context type value source := by
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

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicNestedInputs
