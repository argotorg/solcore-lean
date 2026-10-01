import Solcore.Frontend.SourceCoreCallableContextFrames

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
