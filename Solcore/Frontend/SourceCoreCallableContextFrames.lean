import Solcore.Core.OptionalCell
import Solcore.Core.Check
import Solcore.Core.Renaming

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
