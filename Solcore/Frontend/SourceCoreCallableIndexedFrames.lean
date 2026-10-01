import Solcore.Frontend.SourceCoreCallableContextFrames

/-! Constant-depth ordinary Core callable ancestry carriers. State indices
refer to a separately owned finite metadata table. Decoding a carrier grants
no authority to an index or a descriptor. Integer indices avoid a Word size
bound; table lookup rejects negative and out-of-range indices. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallableIndexedFrames
open Core

structure Layout where
  dataType : DataTypeId
  deriving Repr, DecidableEq

def Layout.type (layout : Layout) : Ty := .namedData layout.dataType
def Layout.empty (layout : Layout) : ConstructorId := ⟨layout.dataType, 0⟩
def Layout.state (layout : Layout) : ConstructorId := ⟨layout.dataType, 1⟩
def Layout.view (layout : Layout) : ConstructorId := ⟨layout.dataType, 2⟩
def Layout.invalid (layout : Layout) : ConstructorId := ⟨layout.dataType, 3⟩
def Layout.definition (_layout : Layout) : DataDefinition :=
  ⟨[.unit, .integer, .product .word (.product .word .integer), .unit]⟩

structure Layout.Registered (definitions : DataEnvironment) (layout : Layout) : Prop where
  lookup : definitions[layout.dataType.index]? = some layout.definition

theorem Layout.Registered.typeWellFormed {definitions : DataEnvironment} {layout : Layout}
    (registered : layout.Registered definitions) : Ty.WellFormed definitions layout.type :=
  .namedData registered.lookup

theorem Layout.Registered.constructorLookup {definitions : DataEnvironment} {layout : Layout}
    (registered : layout.Registered definitions) (index : Nat) :
    definitions.lookupConstructorPayloadType? ⟨layout.dataType, index⟩ =
      layout.definition.constructorPayloadTypes[index]? := by
  simp only [DataEnvironment.lookupConstructorPayloadType?, DataEnvironment.lookupDataType?, registered.lookup]
  rfl

inductive Frame where
  | empty
  | state (index : Int)
  | view (id target : Word) (caller : Int)
  | invalid
  deriving Repr, DecidableEq

def naturalIndex? : Int → Option Nat
  | .ofNat index => some index
  | .negSucc _ => none

def Frame.index? : Frame → Option Nat
  | .state index => naturalIndex? index
  | _ => none

def encode (layout : Layout) : Frame → Value
  | .empty => .constructed layout.empty .unit
  | .state index => .constructed layout.state (.integer index)
  | .view id target caller => .constructed layout.view
      (.pair (.word id) (.pair (.word target) (.integer caller)))
  | .invalid => .constructed layout.invalid .unit

def decode (layout : Layout) : Value → Option Frame
  | .constructed tag .unit =>
      if tag = layout.empty then some .empty
      else if tag = layout.invalid then some .invalid else none
  | .constructed tag (.integer index) =>
      if tag = layout.state then some (.state index) else none
  | .constructed tag (.pair (.word id) (.pair (.word target) (.integer caller))) =>
      if tag = layout.view then some (.view id target caller) else none
  | _ => none

theorem decode_encode (layout : Layout) (frame : Frame) :
    decode layout (encode layout frame) = some frame := by
  cases frame <;> simp [decode, encode, Layout.empty, Layout.invalid]

theorem decode_sound (layout : Layout) (value : Value) (frame : Frame)
    (decoded : decode layout value = some frame) : value = encode layout frame := by
  cases value <;> try (solve | simp [decode] at decoded)
  case constructed tag payload =>
    cases payload <;> try (solve | simp [decode] at decoded)
    case unit =>
      simp only [decode] at decoded
      split at decoded
      · cases decoded; subst tag; rfl
      · split at decoded
        · cases decoded; subst tag; rfl
        · contradiction
    case integer index =>
      simp only [decode] at decoded
      split at decoded
      · cases decoded; subst tag; rfl
      · contradiction
    case pair first second =>
      cases first <;> try (solve | simp [decode] at decoded)
      case word id =>
        cases second <;> try (solve | simp [decode] at decoded)
        case pair target caller =>
          cases target <;> try (solve | simp [decode] at decoded)
          case word target =>
            cases caller <;> try (solve | simp [decode] at decoded)
            case integer caller =>
              simp only [decode] at decoded
              split at decoded
              · cases decoded; subst tag; rfl
              · contradiction

theorem decode_iff (layout : Layout) (value : Value) (frame : Frame) :
    decode layout value = some frame ↔ value = encode layout frame :=
  ⟨decode_sound layout value frame, fun same => same ▸ decode_encode layout frame⟩

theorem encode_runtime_typed {definitions : DataEnvironment} {layout : Layout}
    (world : StoreTyping) (registered : layout.Registered definitions) (frame : Frame) :
    RuntimeValueHasType world (encode layout frame) layout.type definitions := by
  cases frame with
  | empty => exact .constructed (registered.constructorLookup 0) .unit
  | state index => exact .constructed (registered.constructorLookup 1) .integer
  | view id target caller =>
    exact .constructed (registered.constructorLookup 2) (.pair .word (.pair .word .integer))
  | invalid => exact .constructed (registered.constructorLookup 3) .unit

def empty (layout : Layout) : Expr := .construct layout.empty .unit
def state (layout : Layout) (index : Expr) : Expr := .construct layout.state index
def view (layout : Layout) (id target : Word) (caller : Expr) : Expr :=
  .construct layout.view (.pair (.word id) (.pair (.word target) caller))
def invalid (layout : Layout) : Expr := .construct layout.invalid .unit

theorem empty_hasType {definitions : DataEnvironment} {layout : Layout} (context : Context)
    (registered : layout.Registered definitions) : HasType context (empty layout) layout.type definitions :=
  .construct (registered.constructorLookup 0) .unit
theorem state_hasType {definitions : DataEnvironment} {layout : Layout} {context : Context} {index : Expr}
    (registered : layout.Registered definitions) (typed : HasType context index .integer definitions) :
    HasType context (state layout index) layout.type definitions :=
  .construct (registered.constructorLookup 1) typed
theorem view_hasType {definitions : DataEnvironment} {layout : Layout} {context : Context}
    (registered : layout.Registered definitions) (id target : Word) {caller : Expr}
    (typed : HasType context caller .integer definitions) : HasType context (view layout id target caller) layout.type definitions :=
  .construct (registered.constructorLookup 2) (.pair .word (.pair .word typed))
theorem invalid_hasType {definitions : DataEnvironment} {layout : Layout} (context : Context)
    (registered : layout.Registered definitions) : HasType context (invalid layout) layout.type definitions :=
  .construct (registered.constructorLookup 3) .unit

abbrev withFrame := SourceCoreCallableContextFrames.withFrame
def allocate (layout : Layout) (body : Expr) : Expr := .letE (.newCell layout.type (empty layout)) body

end Solcore.Frontend.SourceCoreCallableIndexedFrames
