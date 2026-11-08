import Solcore.Core.Internal.ConventionLaws
import Solcore.Core.Check
import Solcore.Core.Internal.Renaming
import Solcore.Core.LanguageResult
import Solcore.Core.Safety

/-!
# Heap and frame carriers

Heap markers and the ordinary Core frames of callable ancestry, with their decoding. These files
import no source semantics, and they must not: `CallableViewWrappers` in CoreLowering has to stay
outside `Solcore.SourceSemantics.Context`.
-/

section
-- leanmerge: from Solcore.Frontend.SourceCoreCallableContextFrames
/-! Ordinary Core metadata frames for dynamic callable ancestry. This module
supplies finite native carriers and scoped administrative-cell operations.
Ownership of words, source metadata and compiler placement is a separate
artifact boundary. No source evaluator or Core language extension is used. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallableContextFrames
open Core

structure Layout where
  dataType : DataTypeId
  deriving Repr, DecidableEq

def Layout.type (layout : Layout) : Ty := .namedData layout.dataType
def Layout.empty (layout : Layout) : ConstructorId := ⟨layout.dataType, 0⟩
def Layout.named (layout : Layout) : ConstructorId := ⟨layout.dataType, 1⟩
def Layout.lambda (layout : Layout) : ConstructorId := ⟨layout.dataType, 2⟩
def Layout.view (layout : Layout) : ConstructorId := ⟨layout.dataType, 3⟩
def Layout.definition (layout : Layout) : DataDefinition :=
  ⟨[.unit, .word, .product .word layout.type, .product .word (.product .word layout.type)]⟩

structure Layout.Registered (definitions : DataEnvironment) (layout : Layout) : Prop where
  lookup : definitions[layout.dataType.index]? = some layout.definition

theorem Layout.Registered.typeWellFormed {definitions : DataEnvironment} {layout : Layout}
    (registered : layout.Registered definitions) : Ty.WellFormed definitions layout.type :=
  .namedData registered.lookup

private theorem constructorLookup {definitions : DataEnvironment} {layout : Layout}
    (registered : layout.Registered definitions) (index : Nat) :
    definitions.lookupConstructorPayloadType? ⟨layout.dataType, index⟩ =
      layout.definition.constructorPayloadTypes[index]? := by
  simp only [DataEnvironment.lookupConstructorPayloadType?, DataEnvironment.lookupDataType?, registered.lookup]
  rfl

inductive Frame where
  | empty
  | named (origin : Word)
  | lambda (origin : Word) (captured : Frame)
  | view (view target : Word) (parent : Frame)
  deriving Repr, DecidableEq

def encode (layout : Layout) : Frame → Value
  | .empty => .constructed layout.empty .unit
  | .named origin => .constructed layout.named (.word origin)
  | .lambda origin captured => .constructed layout.lambda (.pair (.word origin) (encode layout captured))
  | .view view target parent => .constructed layout.view
      (.pair (.word view) (.pair (.word target) (encode layout parent)))

theorem encode_runtime_typed {definitions : DataEnvironment} {layout : Layout} (world : StoreTyping)
    (registered : layout.Registered definitions) (frame : Frame) :
    RuntimeValueHasType world (encode layout frame) layout.type definitions := by
  induction frame with
  | empty => exact .constructed (constructorLookup registered 0) .unit
  | named origin => exact .constructed (constructorLookup registered 1) .word
  | lambda origin captured ih => exact .constructed (constructorLookup registered 2) (.pair .word ih)
  | view view target parent ih => exact .constructed (constructorLookup registered 3) (.pair .word (.pair .word ih))

def empty (layout : Layout) : Expr := .construct layout.empty .unit
def named (layout : Layout) (origin : Word) : Expr := .construct layout.named (.word origin)
def lambda (layout : Layout) (origin : Word) (captured : Expr) : Expr :=
  .construct layout.lambda (.pair (.word origin) captured)
def view (layout : Layout) (id target : Word) (parent : Expr) : Expr :=
  .construct layout.view (.pair (.word id) (.pair (.word target) parent))

theorem empty_hasType {definitions : DataEnvironment} {layout : Layout} (context : Context)
    (registered : layout.Registered definitions) : HasType context (empty layout) layout.type definitions :=
  .construct (constructorLookup registered 0) .unit

theorem named_hasType {definitions : DataEnvironment} {layout : Layout} (context : Context)
    (registered : layout.Registered definitions) (origin : Word) :
    HasType context (named layout origin) layout.type definitions :=
  .construct (constructorLookup registered 1) .word

theorem lambda_hasType {definitions : DataEnvironment} {layout : Layout} {context : Context}
    (registered : layout.Registered definitions) (origin : Word) {captured : Expr}
    (typed : HasType context captured layout.type definitions) :
    HasType context (lambda layout origin captured) layout.type definitions :=
  .construct (constructorLookup registered 2) (.pair .word typed)

theorem view_hasType {definitions : DataEnvironment} {layout : Layout} {context : Context}
    (registered : layout.Registered definitions) (id target : Word) {parent : Expr}
    (typed : HasType context parent layout.type definitions) :
    HasType context (view layout id target parent) layout.type definitions :=
  .construct (constructorLookup registered 3) (.pair .word (.pair .word typed))

/-- A direct administrative cell is initialized before installing globals. -/
def allocate (layout : Layout) (body : Expr) : Expr := .letE (.newCell layout.type (empty layout)) body

/-- Save the caller's frame, install a lexical frame, run the body, and restore
the caller even when the body returns a language-failure carrier. Temporary
bindings are administrative; this helper does not add source allocations. -/
def withFrame (reference next body : Expr) : Expr :=
  .letE (.loadCell reference)
    (.letE (.storeCell (reference.weakenAt 0) (next.weakenAt 0))
      (.letE ((body.weakenAt 0).weakenAt 0)
        (.letE (.storeCell (((reference.weakenAt 0).weakenAt 0).weakenAt 0) (.var 2)) (.var 1))))

private theorem atFront {definitions : DataEnvironment} {context : Context} {expression : Expr} {type : Ty}
    (typed : HasType context expression type definitions) (inserted : Ty) :
    HasType (inserted :: context) (expression.weakenAt 0) type definitions := by
  simpa [Context.insertAt] using typed.weakenAt (inserted := inserted) 0

theorem withFrame_hasType {definitions : DataEnvironment} {context : Context} {frame result : Ty}
    {reference next body : Expr} (referenceTyped : HasType context reference (.cell frame) definitions)
    (nextTyped : HasType context next frame definitions) (bodyTyped : HasType context body result definitions) :
    HasType context (withFrame reference next body) result definitions := by
  apply HasType.letE (.loadCell referenceTyped)
  apply HasType.letE (.storeCell (atFront referenceTyped frame) (atFront nextTyped frame))
  apply HasType.letE (atFront (atFront bodyTyped frame) .unit)
  apply HasType.letE (.storeCell (atFront (atFront (atFront referenceTyped frame) .unit) result) (.var rfl))
  exact .var rfl

/-- Keep the leading read view only if it belongs to this exact lambda. The
lexically captured ancestry supplies the parent instead of the caller stack. -/
def lambdaFrame (layout : Layout) (origin : Word) (captured current : Expr) : Expr :=
  let plain := (lambda layout origin captured).weakenAt 0
  .matchData layout.dataType layout.type current [plain, plain, plain,
    .ifE (.binary .wordEq (.first (.second (.var 0))) (.word origin))
      (lambda layout origin (.construct layout.view
        (.pair (.first (.var 0)) (.pair (.word origin) (captured.weakenAt 0))))) plain]

theorem lambdaFrame_hasType {definitions : DataEnvironment} {layout : Layout} {context : Context}
    (registered : layout.Registered definitions) (origin : Word) {captured current : Expr}
    (capturedTyped : HasType context captured layout.type definitions)
    (currentTyped : HasType context current layout.type definitions) :
    HasType context (lambdaFrame layout origin captured current) layout.type definitions := by
  apply HasType.matchData registered.lookup registered.typeWellFormed currentTyped
  apply BranchesHaveType.cons (atFront (lambda_hasType registered origin capturedTyped) .unit)
  apply BranchesHaveType.cons (atFront (lambda_hasType registered origin capturedTyped) .word)
  apply BranchesHaveType.cons (atFront (lambda_hasType registered origin capturedTyped) (.product .word layout.type))
  apply BranchesHaveType.cons
  · apply HasType.ifE (.binary (.first (.second (.var rfl))) .word)
    · apply lambda_hasType registered origin
      apply HasType.construct (constructorLookup registered 3)
      exact .pair (.first (.var rfl))
        (.pair .word (atFront capturedTyped (.product .word (.product .word layout.type))))
    · exact atFront (lambda_hasType registered origin capturedTyped) (.product .word (.product .word layout.type))
  · exact .nil

end Solcore.Frontend.SourceCoreCallableContextFrames
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreCallableContextFrameCodec
/-! Exact decoding of the ordinary nominal callable-frame carrier. This
recognizes values only; source ownership and execution history are separate
receipts supplied by the enclosing compiler artifact. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallableContextFrameCodec
open Core SourceCoreCallableContextFrames

def decode (layout : Layout) : Value → Option SourceCoreCallableContextFrames.Frame
  | .constructed constructor .unit => if constructor = layout.empty then some .empty else none
  | .constructed constructor (.word origin) =>
      if constructor = layout.named then some (.named origin) else none
  | .constructed constructor (.pair (.word first) second) =>
      if constructor = layout.lambda then (decode layout second).map (.lambda first)
      else if constructor = layout.view then
        match second with
        | .pair (.word target) parent => (decode layout parent).map (.view first target)
        | _ => none
      else none
  | _ => none

theorem decode_encode (layout : Layout) (frame : SourceCoreCallableContextFrames.Frame) :
    decode layout (encode layout frame) = some frame := by
  induction frame with
  | empty => simp [decode, encode]
  | named origin => simp [decode, encode]
  | lambda origin captured ih =>
      cases captured <;> simp [decode, encode, Layout.lambda, Layout.empty, Layout.named, Layout.view, *] at * <;> assumption
  | view view target parent ih =>
      simp [decode, encode, Layout.lambda, Layout.view, ih]

theorem decode_sound (layout : Layout) (value : Value) (frame : SourceCoreCallableContextFrames.Frame)
    (decoded : decode layout value = some frame) : value = encode layout frame := by
  revert frame
  induction value using decode.induct layout with
  | case1 =>
      intro frame decoded
      simp [decode] at decoded
      subst frame
      rfl
  | case2 constructor different =>
      intro frame decoded
      simp [decode, different] at decoded
  | case3 origin =>
      intro frame decoded
      simp [decode] at decoded
      subst frame
      rfl
  | case4 constructor origin different =>
      intro frame decoded
      simp [decode, different] at decoded
  | case5 first second ih =>
      intro frame decoded
      rw [decode.eq_def] at decoded
      simp only [↓reduceIte] at decoded
      cases observed : decode layout second with
      | none => simp [observed] at decoded
      | some captured =>
          simp [observed] at decoded
          subst frame
          rw [encode, ih captured observed]
  | case6 first target parent different ih =>
      intro frame decoded
      simp [decode, different] at decoded
      cases observed : decode layout parent with
      | none => simp [observed] at decoded
      | some captured =>
          simp [observed] at decoded
          subst frame
          rw [encode, ih captured observed]
  | case7 first second malformed different =>
      intro frame decoded
      rw [decode.eq_def] at decoded
      simp only [different, ↓reduceIte] at decoded
      contradiction
  | case8 constructor first second notLambda notView =>
      intro frame decoded
      rw [decode.eq_def] at decoded
      simp [notLambda, notView] at decoded
  | case9 value notEmpty notNamed notPair =>
      intro frame decoded
      rw [decode.eq_def] at decoded
      split at decoded <;> simp_all

theorem decode_iff (layout : Layout) (value : Value) (frame : SourceCoreCallableContextFrames.Frame) :
    decode layout value = some frame ↔ value = encode layout frame :=
  ⟨decode_sound layout value frame, fun same => same ▸ decode_encode layout frame⟩

end Solcore.Frontend.SourceCoreCallableContextFrameCodec
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreCallableIndexedFrames
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
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreCallableNativeSlots
/-! Pure native environment checks shared by callable profiles. Receipts here
prove equality to the supplied installed code, heap and reference types. They
do not authenticate a source owner, a descriptor word, or execution history.
The enclosing artifact must supply its exact compilation receipt separately.
-/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallableNativeSlots
open Core

/-- Public native data paths stop at closures. Saved environments are never
treated as values returned by a source computation. -/
inductive Subvalue (value : Value) : Value → Prop where
  | root : Subvalue value value
  | pairLeft {left right : Value} (inside : Subvalue value left) : Subvalue value (.pair left right)
  | pairRight {left right : Value} (inside : Subvalue value right) : Subvalue value (.pair left right)
  | inLeft {type : Ty} {payload : Value} (inside : Subvalue value payload) : Subvalue value (.inLeft type payload)
  | inRight {type : Ty} {payload : Value} (inside : Subvalue value payload) : Subvalue value (.inRight type payload)
  | constructed {constructor : ConstructorId} {payload : Value} (inside : Subvalue value payload) :
      Subvalue value (.constructed constructor payload)

inductive Error where
  | missingGlobal (index : Nat)
  | globalTemplateMismatch (index : Nat)
  | globalsMismatch (location : Nat)
  | missingReference (index : Nat)
  | referenceMismatch (index : Nat)
  | referenceWorldMismatch (location : Nat)
  deriving Repr

/-- Input code has already undergone the caller's actual installation
renaming. Global positions are physical indices, independent of source heap
locations. Every installed closure saves the same globals and protocol tail. -/
def expectedGlobals (signatures : List (Ty × Ty)) (installed : List Expr)
    (environment : Environment) (base : Nat) : Except Error (List (Nat × Value)) := do
  if installed.length != signatures.length then throw (.missingGlobal 0)
  signatures.zipIdx.mapM fun ((parameter, result), index) => do
    let closure ← match installed[index]? with
      | some closure => pure closure | none => throw (.missingGlobal index)
    let .lambda actualParameter actualResult body := closure
      | throw (.globalTemplateMismatch index)
    if actualParameter != parameter || actualResult != LanguageResult.resultType result then
      throw (.globalTemplateMismatch index)
    pure (base + signatures.length - 1 - index,
      .inRight .unit (.closure parameter (LanguageResult.resultType result) body
        (List.replicate index .unit ++ environment)))

structure Globals (signatures : List (Ty × Ty)) (installed : List Expr)
    (environment : Environment) (base : Nat) (store : Store) where private mk ::
  slots : List (Nat × Value)
  generated : expectedGlobals signatures installed environment base = .ok slots
  exact : slots.all (fun (location, value) => decide (store[location]? = some value)) = true

/-- Runtime checking consumes precomputed code slots. No installation
renaming, signature traversal or source traversal is needed here. -/
def checkPreparedGlobals {signatures : List (Ty × Ty)} {installed : List Expr}
    {environment : Environment} {base : Nat} (slots : List (Nat × Value))
    (generated : expectedGlobals signatures installed environment base = .ok slots) (store : Store) :
    Except Error (Globals signatures installed environment base store) := do
  if exact : slots.all (fun (location, value) => decide (store[location]? = some value)) = true then
    pure ⟨slots, generated, exact⟩
  else
    match slots.find? (fun (location, value) => decide (store[location]? != some value)) with
    | some (location, _) => throw (.globalsMismatch location)
    | none => throw (.globalsMismatch base)

def checkGlobals (signatures : List (Ty × Ty)) (installed : List Expr)
    (environment : Environment) (base : Nat) (store : Store) :
    Except Error (Globals signatures installed environment base store) := do
  match generated : expectedGlobals signatures installed environment base with
  | .error error => throw error
  | .ok slots => checkPreparedGlobals slots generated store

theorem Globals.slot_exact {signatures : List (Ty × Ty)} {installed : List Expr}
    {environment : Environment} {base : Nat} {store : Store}
    (checked : Globals signatures installed environment base store)
    {location : Nat} {value : Value} (member : (location, value) ∈ checked.slots) :
    store[location]? = some value :=
  of_decide_eq_true (List.all_eq_true.mp checked.exact _ member)

structure Reference (environment : Environment) (world : StoreTyping) (index : Nat) (payloadType : Ty) where private mk ::
  location : Nat
  exact : environment[index]? = some (.cellRef (OptionalCell.cellType payloadType) location)
  worldExact : world[location]? = some (OptionalCell.cellType payloadType)

def reference (environment : Environment) (world : StoreTyping) (index : Nat) (payloadType : Ty) :
    Except Error (Reference environment world index payloadType) := do
  let value ← match environment[index]? with
    | some value => pure value | none => throw (.missingReference index)
  let .cellRef actual location := value | throw (.referenceMismatch index)
  if actual != OptionalCell.cellType payloadType then throw (.referenceMismatch index)
  if exact : environment[index]? = some (.cellRef (OptionalCell.cellType payloadType) location) then
    if worldExact : world[location]? = some (OptionalCell.cellType payloadType) then
      pure ⟨location, exact, worldExact⟩
    else throw (.referenceWorldMismatch location)
  else throw (.referenceMismatch index)

private theorem environment_slot_typed {definitions : DataEnvironment} {world : StoreTyping}
    {environment : Environment} {context : Context} {index : Nat} {value : Value}
    (typed : RuntimeEnvironmentHasTypes world environment context definitions)
    (found : environment[index]? = some value) : RuntimeValueHasType world value value.type definitions := by
  induction typed using RuntimeEnvironmentHasTypes.rec
      (motive_1 := fun _ _ _ _ => True) generalizing index with
  | unit | bool | word | integer | pair | inLeft | inRight | closure | cellRef | constructed => trivial
  | nil => simp at found
  | cons valueTyped _ _ tailIH =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at found
      subst value
      rw [valueTyped.type_eq]
      exact valueTyped
    | succ index => exact tailIH (by simpa using found)

/-- Inverting the saved environment preserves actual runtime typing. The
requested slot is checked again by the owning profile for its expected type. -/
theorem saved_slot_typed {definitions : DataEnvironment} {world : StoreTyping}
    {environment : Environment} {body : Expr} {parameter result : Ty} {index : Nat} {value : Value}
    (typed : RuntimeValueHasType world (.closure parameter result body environment) (.function parameter result) definitions)
    (found : environment[index]? = some value) : RuntimeValueHasType world value value.type definitions := by
  cases typed with
  | closure environmentTyped _ => exact environment_slot_typed environmentTyped found

end Solcore.Frontend.SourceCoreCallableNativeSlots
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreCallableNativeSubvalues
/-! Locate native values in public data without entering closure environments.
Each successful lookup retains its structural path, and runtime typing follows
from the enclosing typed result or source-cell payload. This pure operation
supplies no source-code, allocation or execution-history authority itself.
-/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallableNativeSubvalues
open Core SourceCoreCallableNativeSlots

structure Path (value root : Value) : Type where
  related : Subvalue value root

/-- Saved closure environments remain outside public data paths. -/
def find (value : Value) : (root : Value) → Option (Path value root)
  | .pair left right =>
    if same : value = .pair left right then some ⟨same ▸ .root⟩
    else match find value left with
      | some inside => some ⟨.pairLeft inside.related⟩
      | none => (find value right).map fun inside => ⟨.pairRight inside.related⟩
  | .inLeft type payload =>
    if same : value = .inLeft type payload then some ⟨same ▸ .root⟩
    else (find value payload).map fun inside => ⟨.inLeft inside.related⟩
  | .inRight type payload =>
    if same : value = .inRight type payload then some ⟨same ▸ .root⟩
    else (find value payload).map fun inside => ⟨.inRight inside.related⟩
  | .constructed constructor payload =>
    if same : value = .constructed constructor payload then some ⟨same ▸ .root⟩
    else (find value payload).map fun inside => ⟨.constructed inside.related⟩
  | root => if same : value = root then some ⟨same ▸ .root⟩ else none

/-- A public data path inherits its actual finite-world native typing. -/
theorem runtime_typed {definitions : DataEnvironment} {world : StoreTyping}
    {value root : Value} {type : Ty} (inside : Subvalue value root)
    (typed : RuntimeValueHasType world root type definitions) :
    RuntimeValueHasType world value value.type definitions := by
  induction inside generalizing type with
  | root => simpa only [typed.type_eq] using typed
  | pairLeft inside ih => cases typed with | pair left right => exact ih left
  | pairRight inside ih => cases typed with | pair left right => exact ih right
  | inLeft inside ih => cases typed with | inLeft payload => exact ih payload
  | inRight inside ih => cases typed with | inRight payload => exact ih payload
  | constructed inside ih => cases typed with | constructed _ payload => exact ih payload

end Solcore.Frontend.SourceCoreCallableNativeSubvalues
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreCallablePairedFrames
/-! Successor ordinary-Core ancestry carrier. A generalized read saves its
caller metadata at the time of the read. Application pairs that caller with
the original lambda's lexical creation metadata. The two parents are kept in
their original order and never rebased onto one another.

This library supplies native syntax and typing only. Word ownership, source
metadata transitions and actual execution provenance belong to artifact
receipts. The existing single-parent profile remains a separate type/profile.
-/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallablePairedFrames
open Core

structure Layout where
  dataType : DataTypeId
  deriving Repr, DecidableEq

def Layout.type (layout : Layout) : Ty := .namedData layout.dataType
def Layout.empty (layout : Layout) : ConstructorId := ⟨layout.dataType, 0⟩
def Layout.named (layout : Layout) : ConstructorId := ⟨layout.dataType, 1⟩
def Layout.lambda (layout : Layout) : ConstructorId := ⟨layout.dataType, 2⟩
def Layout.view (layout : Layout) : ConstructorId := ⟨layout.dataType, 3⟩
def Layout.appliedView (layout : Layout) : ConstructorId := ⟨layout.dataType, 4⟩
def Layout.definition (layout : Layout) : DataDefinition :=
  ⟨[.unit, .word, .product .word layout.type,
    .product .word (.product .word layout.type),
    .product .word (.product .word (.product layout.type layout.type))]⟩

structure Layout.Registered (definitions : DataEnvironment) (layout : Layout) : Prop where
  lookup : definitions[layout.dataType.index]? = some layout.definition

theorem Layout.Registered.typeWellFormed {definitions : DataEnvironment} {layout : Layout}
    (registered : layout.Registered definitions) : Ty.WellFormed definitions layout.type :=
  .namedData registered.lookup

private theorem constructorLookup {definitions : DataEnvironment} {layout : Layout}
    (registered : layout.Registered definitions) (index : Nat) :
    definitions.lookupConstructorPayloadType? ⟨layout.dataType, index⟩ =
      layout.definition.constructorPayloadTypes[index]? := by
  simp only [DataEnvironment.lookupConstructorPayloadType?, DataEnvironment.lookupDataType?, registered.lookup]
  rfl

inductive Frame where
  | empty
  | named (origin : Word)
  | lambda (origin : Word) (captured : Frame)
  | view (view target : Word) (caller : Frame)
  | appliedView (view target : Word) (caller lexical : Frame)
  deriving Repr, DecidableEq

def encode (layout : Layout) : Frame → Value
  | .empty => .constructed layout.empty .unit
  | .named origin => .constructed layout.named (.word origin)
  | .lambda origin captured => .constructed layout.lambda (.pair (.word origin) (encode layout captured))
  | .view view target caller => .constructed layout.view
      (.pair (.word view) (.pair (.word target) (encode layout caller)))
  | .appliedView view target caller lexical => .constructed layout.appliedView
      (.pair (.word view) (.pair (.word target) (.pair (encode layout caller) (encode layout lexical))))

theorem encode_runtime_typed {definitions : DataEnvironment} {layout : Layout} (world : StoreTyping)
    (registered : layout.Registered definitions) (frame : Frame) :
    RuntimeValueHasType world (encode layout frame) layout.type definitions := by
  induction frame with
  | empty => exact .constructed (constructorLookup registered 0) .unit
  | named origin => exact .constructed (constructorLookup registered 1) .word
  | lambda origin captured ih => exact .constructed (constructorLookup registered 2) (.pair .word ih)
  | view view target caller ih => exact .constructed (constructorLookup registered 3) (.pair .word (.pair .word ih))
  | appliedView view target caller lexical callerIH lexicalIH =>
    exact .constructed (constructorLookup registered 4) (.pair .word (.pair .word (.pair callerIH lexicalIH)))

def empty (layout : Layout) : Expr := .construct layout.empty .unit
def named (layout : Layout) (origin : Word) : Expr := .construct layout.named (.word origin)
def lambda (layout : Layout) (origin : Word) (captured : Expr) : Expr :=
  .construct layout.lambda (.pair (.word origin) captured)
def view (layout : Layout) (id target : Word) (caller : Expr) : Expr :=
  .construct layout.view (.pair (.word id) (.pair (.word target) caller))
def appliedView (layout : Layout) (id target : Word) (caller lexical : Expr) : Expr :=
  .construct layout.appliedView (.pair (.word id) (.pair (.word target) (.pair caller lexical)))

theorem empty_hasType {definitions : DataEnvironment} {layout : Layout} (context : Context)
    (registered : layout.Registered definitions) : HasType context (empty layout) layout.type definitions :=
  .construct (constructorLookup registered 0) .unit
theorem named_hasType {definitions : DataEnvironment} {layout : Layout} (context : Context)
    (registered : layout.Registered definitions) (origin : Word) : HasType context (named layout origin) layout.type definitions :=
  .construct (constructorLookup registered 1) .word
theorem lambda_hasType {definitions : DataEnvironment} {layout : Layout} {context : Context}
    (registered : layout.Registered definitions) (origin : Word) {captured : Expr}
    (typed : HasType context captured layout.type definitions) : HasType context (lambda layout origin captured) layout.type definitions :=
  .construct (constructorLookup registered 2) (.pair .word typed)
theorem view_hasType {definitions : DataEnvironment} {layout : Layout} {context : Context}
    (registered : layout.Registered definitions) (id target : Word) {caller : Expr}
    (typed : HasType context caller layout.type definitions) : HasType context (view layout id target caller) layout.type definitions :=
  .construct (constructorLookup registered 3) (.pair .word (.pair .word typed))
theorem appliedView_hasType {definitions : DataEnvironment} {layout : Layout} {context : Context}
    (registered : layout.Registered definitions) (id target : Word) {caller lexical : Expr}
    (callerTyped : HasType context caller layout.type definitions)
    (lexicalTyped : HasType context lexical layout.type definitions) :
    HasType context (appliedView layout id target caller lexical) layout.type definitions :=
  .construct (constructorLookup registered 4) (.pair .word (.pair .word (.pair callerTyped lexicalTyped)))

abbrev withFrame := SourceCoreCallableContextFrames.withFrame

def allocate (layout : Layout) (body : Expr) : Expr := .letE (.newCell layout.type (empty layout)) body

private theorem atFront {definitions : DataEnvironment} {context : Context} {expression : Expr} {type : Ty}
    (typed : HasType context expression type definitions) (inserted : Ty) :
    HasType (inserted :: context) (expression.weakenAt 0) type definitions := by
  simpa [Context.insertAt] using typed.weakenAt (inserted := inserted) 0

/-- A matching incoming view retains its saved caller and the lambda's
lexical snapshot. Other incoming states use the lambda's lexical snapshot. -/
def lambdaFrame (layout : Layout) (origin : Word) (lexical current : Expr) : Expr :=
  let plain := (lambda layout origin lexical).weakenAt 0
  .matchData layout.dataType layout.type current [plain, plain, plain,
    .ifE (.binary .wordEq (.first (.second (.var 0))) (.word origin))
      (.construct layout.appliedView
        (.pair (.first (.var 0)) (.pair (.word origin)
          (.pair (.second (.second (.var 0))) (lexical.weakenAt 0))))) plain,
    plain]

def selectedFrame (origin : Word) (lexical : Frame) : Frame → Frame
  | .view id target caller => if target = origin then .appliedView id origin caller lexical else .lambda origin lexical
  | _ => .lambda origin lexical

theorem lambdaFrame_hasType {definitions : DataEnvironment} {layout : Layout} {context : Context}
    (registered : layout.Registered definitions) (origin : Word) {lexical current : Expr}
    (lexicalTyped : HasType context lexical layout.type definitions)
    (currentTyped : HasType context current layout.type definitions) :
    HasType context (lambdaFrame layout origin lexical current) layout.type definitions := by
  apply HasType.matchData registered.lookup registered.typeWellFormed currentTyped
  apply BranchesHaveType.cons (atFront (lambda_hasType registered origin lexicalTyped) .unit)
  apply BranchesHaveType.cons (atFront (lambda_hasType registered origin lexicalTyped) .word)
  apply BranchesHaveType.cons (atFront (lambda_hasType registered origin lexicalTyped) (.product .word layout.type))
  apply BranchesHaveType.cons
  · apply HasType.ifE (.binary (.first (.second (.var rfl))) .word)
    · apply HasType.construct (constructorLookup registered 4)
      exact .pair (.first (.var rfl)) (.pair .word
        (.pair (.second (.second (.var rfl))) (atFront lexicalTyped (.product .word (.product .word layout.type)))))
    · exact atFront (lambda_hasType registered origin lexicalTyped) (.product .word (.product .word layout.type))
  · exact .cons (atFront (lambda_hasType registered origin lexicalTyped)
      (.product .word (.product .word (.product layout.type layout.type)))) .nil

end Solcore.Frontend.SourceCoreCallablePairedFrames
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreCallableViewWrappers
/-! A source callable view is carried by an ordinary transparent Core lambda.
The original callable identity and contract descriptor remain unchanged. Its
body contains a bounded word manifest and applies the original payload; it
allocates no cells and introduces no Core syntax or runtime evaluator.

The parser recognizes an exact wrapper shape and copied tags. It establishes
no source provenance: a caller must authenticate the returned view word and
original carrier against its own compiler metadata. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallableViewWrappers
open Core

/-- After the manifest binder: original carrier is slot 2, argument is slot 1. -/
def body (view : Word) : Expr :=
  .letE (.word view) (.apply (.second (.first (.var 2))) (.var 1))

/-- Under the successful read's original-carrier binder. -/
def repack (parameter result : Ty) (view : Word) : Expr :=
  .pair (.pair (.first (.first (.var 0)))
    (.lambda parameter (LanguageResult.resultType result) (body view)))
    (.second (.var 0))

def lower (parameter result : Ty) (view : Word) (read : Expr) : Expr :=
  LanguageResult.bind (CallableContract.functionType parameter result) read
    (LanguageResult.success (repack parameter result view))

def originalValue (identity payload : Value) (contract : Word) : Value :=
  .pair (.pair identity payload) (.word contract)

def wrappedValue (parameter result : Ty) (view : Word) (identity payload : Value)
    (contract : Word) (outer : Environment) : Value :=
  .pair (.pair identity (.closure parameter (LanguageResult.resultType result) (body view)
    (originalValue identity payload contract :: outer))) (.word contract)

def bodyView? : Expr → Option Word
  | .letE (.word view) (.apply (.second (.first (.var 2))) (.var 1)) => some view
  | _ => none

/-- Exact shape only. In particular the original carrier and the complete
outer environment are retained, without traversing their captured references. -/
structure Parsed (parameter result : Ty) (value : Value) where
  view : Word
  identity : Value
  payload : Value
  contract : Word
  outer : Environment
  shape : value = wrappedValue parameter result view identity payload contract outer
  deriving Repr

def Parsed.original {parameter result : Ty} {value : Value} (parsed : Parsed parameter result value) : Value :=
  originalValue parsed.identity parsed.payload parsed.contract

def parse? (parameter result : Ty) (value : Value) : Option (Parsed parameter result value) :=
  match observed : value with
  | .pair (.pair _ (.closure _ _ code (original :: outer))) (.word _) => do
    let view ← bodyView? code
    let .pair (.pair identity payload) (.word contract) := original | none
    if shape : value = wrappedValue parameter result view identity payload contract outer then
      some ⟨view, identity, payload, contract, outer, observed.symm.trans shape⟩
    else none
  | _ => none

theorem parse_wrapped (parameter result : Ty) (view : Word) (identity payload : Value)
    (contract : Word) (outer : Environment) :
    (parse? parameter result (wrappedValue parameter result view identity payload contract outer)).isSome = true := by
  simp [parse?, wrappedValue, originalValue, bodyView?, body]

theorem Parsed.original_exact {parameter result : Ty} {value : Value}
    (parsed : Parsed parameter result value) :
    value = .pair (.pair parsed.identity
      (.closure parameter (LanguageResult.resultType result) (body parsed.view)
        (parsed.original :: parsed.outer))) (.word parsed.contract) := parsed.shape

end Solcore.Frontend.SourceCoreCallableViewWrappers
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreHeapMarkers
/-! Source-visible allocations use an artifact-owned nominal marker followed
by an ordinary optional payload cell. A marker's payload records actual lexical
references selected by its compiler capture-layout receipt. Its data identity
indexes the artifact's static allocation metadata.

The allocation expression returns only the payload reference. Marker bindings
stay inside that expression, so the caller's lexical environment is unchanged.
This library does not authenticate arbitrary marker IDs, export source heaps,
or modify any compiler allocation site yet. -/

set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreHeapMarkers
open Core

structure Layout where
  dataType : DataTypeId
  captureType : Ty
  deriving Repr, BEq, DecidableEq

def Layout.type (layout : Layout) : Ty := .namedData layout.dataType
def Layout.definition (layout : Layout) : DataDefinition := ⟨[layout.captureType]⟩
def Layout.constructor (layout : Layout) : ConstructorId := ⟨layout.dataType, 0⟩
def marker (layout : Layout) (captures : Expr) : Expr := .construct layout.constructor captures
def markerValue (layout : Layout) (captures : Value) : Value := .constructed layout.constructor captures

structure Layout.Registered (definitions : DataEnvironment) (layout : Layout) : Prop where
  capturesWellFormed : Ty.WellFormed definitions layout.captureType
  lookup : definitions[layout.dataType.index]? = some layout.definition

theorem Layout.Registered.typeWellFormed {definitions : DataEnvironment} {layout : Layout}
    (registered : layout.Registered definitions) : Ty.WellFormed definitions layout.type :=
  .namedData registered.lookup

theorem Layout.Registered.payloadLookup {definitions : DataEnvironment} {layout : Layout}
    (registered : layout.Registered definitions) :
    definitions.lookupConstructorPayloadType? layout.constructor = some layout.captureType := by
  simp [DataEnvironment.lookupConstructorPayloadType?, DataEnvironment.lookupDataType?,
    Layout.constructor, registered.lookup, Layout.definition]

theorem marker_hasType {definitions : DataEnvironment} {layout : Layout}
    {context : Core.Context} {captures : Expr}
    (registered : layout.Registered definitions)
    (typed : HasType context captures layout.captureType definitions) :
    HasType context (marker layout captures) layout.type definitions :=
  .construct registered.payloadLookup typed

/-- The initializer succeeds before either allocation. The marker captures
the caller's existing lexical references, beneath the temporary result binder. -/
def allocateInitialized (layout : Layout) (payloadType : Ty) (captures initializer : Expr) : Expr :=
  .letE initializer
    (.letE (.newCell layout.type (marker layout (captures.weakenAt 0)))
      (OptionalCell.allocateInitialized payloadType (.var 1)))

def allocate (layout : Layout) (payloadType : Ty) (captures : Expr) : Expr :=
  .letE (.newCell layout.type (marker layout captures)) (OptionalCell.allocate payloadType)

theorem allocateInitialized_hasType {definitions : DataEnvironment} {layout : Layout}
    {context : Core.Context} {payloadType : Ty} {captures initializer : Expr}
    (registered : layout.Registered definitions)
    (capturesTyped : HasType context captures layout.captureType definitions)
    (initializerTyped : HasType context initializer payloadType definitions) :
    HasType context (allocateInitialized layout payloadType captures initializer)
      (OptionalCell.referenceType payloadType) definitions := by
  apply HasType.letE initializerTyped
  apply HasType.letE
    (.newCell (marker_hasType registered
      (by simpa [Context.insertAt] using capturesTyped.weakenAt (inserted := payloadType) 0)))
  exact OptionalCell.allocateInitialized_hasType (.var rfl)

theorem allocate_hasType {definitions : DataEnvironment} {layout : Layout}
    {context : Core.Context} {payloadType : Ty} {captures : Expr}
    (registered : layout.Registered definitions)
    (capturesTyped : HasType context captures layout.captureType definitions)
    (payloadWellFormed : Ty.WellFormed definitions payloadType) :
    HasType context (allocate layout payloadType captures)
      (OptionalCell.referenceType payloadType) definitions :=
  .letE (.newCell (marker_hasType registered capturesTyped))
    (OptionalCell.allocate_hasType payloadWellFormed)

/-- Capture selection is pure. Both cells are appended after initializer
effects, with no allocation or write between the marker and source payload. -/
theorem allocateInitialized_evaluates {layout : Layout} {payloadType : Ty}
    {environment : Environment} {before middle : Store} {captures initializer : Expr}
    {captured payload : Value}
    (initialized : Evaluates environment before initializer payload middle)
    (selected : Evaluates (payload :: environment) middle (captures.weakenAt 0) captured middle) :
    Evaluates environment before (allocateInitialized layout payloadType captures initializer)
      (.cellRef (OptionalCell.cellType payloadType) (middle.length + 1))
      ((middle ++ [markerValue layout captured]) ++ [.inRight .unit payload]) := by
  simpa only [allocateInitialized, marker, markerValue, List.length_append, List.length_singleton] using
    (Evaluates.letE initialized
      (Evaluates.letE (Evaluates.newCell (Evaluates.construct selected))
        (OptionalCell.allocateInitialized_evaluates
          (Evaluates.var (index := 1) (by rfl)))))

theorem allocate_evaluates {layout : Layout} {payloadType : Ty}
    {environment : Environment} {store : Store} {captures : Expr} {captured : Value}
    (selected : Evaluates environment store captures captured store) :
    Evaluates environment store (allocate layout payloadType captures)
      (.cellRef (OptionalCell.cellType payloadType) (store.length + 1))
      ((store ++ [markerValue layout captured]) ++ [.inLeft payloadType .unit]) := by
  simpa only [allocate, marker, markerValue, List.length_append, List.length_singleton] using
    (Evaluates.letE (Evaluates.newCell (Evaluates.construct selected))
      (OptionalCell.allocate_evaluates payloadType
        (.cellRef layout.type store.length :: environment) (store ++ [markerValue layout captured])))

def completedPair (layout : Layout) (store : Store) (index : Nat) : Option (Value × Value) := do
  let .constructed constructor captures ← store[index]? | none
  if constructor = layout.constructor then
    pure (captures, ← store[index + 1]?)
  else none

/-- A partially executed allocation contributes no source cell until its
adjacent payload exists. This is a store observation, not a resume theorem. -/
theorem unfinished_not_completed (layout : Layout) (store : Store) (captured : Value) :
    completedPair layout (store ++ [markerValue layout captured]) store.length = none := by
  simp [completedPair, markerValue]

theorem completed_pair (layout : Layout) (store : Store) (captured payload : Value) :
    completedPair layout ((store ++ [markerValue layout captured]) ++ [payload]) store.length =
      some (captured, payload) := by
  simp [completedPair, markerValue, List.length_append]

theorem prefix_unchanged (store : Store) (layout : Layout) (captured payload : Value) :
    (((store ++ [markerValue layout captured]) ++ [payload]).take store.length) = store := by
  simp [List.append_assoc]

end Solcore.Frontend.SourceCoreHeapMarkers
end
