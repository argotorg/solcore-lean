import Solcore.Core.Primitive
import Solcore.Core.Typing
import Solcore.Core.Store
import Solcore.Core.Eval
import Solcore.Core.Safety

set_option autoImplicit false

namespace Solcore.Core

abbrev Renaming := Nat → Nat

namespace Renaming

def id : Renaming := fun index => index

def comp (outer inner : Renaming) : Renaming :=
  fun index => outer (inner index)

def lift (mapping : Renaming) : Renaming
  | 0 => 0
  | index + 1 => mapping index + 1

def insertion (cutoff : Nat) : Renaming :=
  fun index => if cutoff ≤ index then index + 1 else index

@[simp] theorem lift_id : lift id = id := by
  funext index
  cases index <;> rfl

@[simp] theorem lift_comp (outer inner : Renaming) :
    lift (comp outer inner) = comp (lift outer) (lift inner) := by
  funext index
  cases index <;> rfl

@[simp] theorem lift_insertion (cutoff : Nat) :
    lift (insertion cutoff) = insertion (cutoff + 1) := by
  funext index
  cases index with
  | zero => simp [lift, insertion]
  | succ index =>
      by_cases shifted : cutoff ≤ index <;>
        simp [lift, insertion, Nat.succ_le_succ_iff, shifted]

@[simp] theorem lift_comp_insertion_zero (mapping : Renaming) :
    comp mapping.lift (insertion 0) = comp (insertion 0) mapping := by
  funext index
  simp [comp, lift, insertion]

end Renaming

mutual

  def Expr.rename (expr : Expr) (mapping : Renaming) : Expr :=
    match expr with
    | .unit => .unit
    | .bool value => .bool value
    | .word value => .word value
    | .var index => .var (mapping index)
    | .pair left right => .pair (left.rename mapping) (right.rename mapping)
    | .first operand => .first (operand.rename mapping)
    | .second operand => .second (operand.rename mapping)
    | .lambda parameterType resultType body =>
        .lambda parameterType resultType (body.rename mapping.lift)
    | .apply function argument =>
        .apply (function.rename mapping) (argument.rename mapping)
    | .inLeft rightType payload => .inLeft rightType (payload.rename mapping)
    | .inRight leftType payload => .inRight leftType (payload.rename mapping)
    | .caseE scrutinee leftBranch rightBranch =>
        .caseE
          (scrutinee.rename mapping)
          (leftBranch.rename mapping.lift)
          (rightBranch.rename mapping.lift)
    | .newCell elementType initializer =>
        .newCell elementType (initializer.rename mapping)
    | .loadCell reference => .loadCell (reference.rename mapping)
    | .storeCell reference value =>
        .storeCell (reference.rename mapping) (value.rename mapping)
    | .construct constructor payload =>
        .construct constructor (payload.rename mapping)
    | .matchData dataType resultType scrutinee branches =>
        .matchData dataType resultType
          (scrutinee.rename mapping)
          (Expr.renameList branches mapping.lift)
    | .unary op operand => .unary op (operand.rename mapping)
    | .binary op left right =>
        .binary op (left.rename mapping) (right.rename mapping)
    | .ternary op firstExpr secondExpr thirdExpr =>
        .ternary op (firstExpr.rename mapping) (secondExpr.rename mapping)
          (thirdExpr.rename mapping)
    | .letE value body =>
        .letE (value.rename mapping) (body.rename mapping.lift)
    | .ifE condition thenBranch elseBranch =>
        .ifE
          (condition.rename mapping)
          (thenBranch.rename mapping)
          (elseBranch.rename mapping)

  def Expr.renameList (expressions : List Expr) (mapping : Renaming) : List Expr :=
    match expressions with
    | [] => []
    | expression :: rest =>
        expression.rename mapping :: Expr.renameList rest mapping

end

mutual

  @[simp] theorem Expr.rename_id : ∀ expr : Expr, expr.rename Renaming.id = expr
    | .unit | .bool _ | .word _ | .var _ => rfl
    | .pair left right
    | .apply left right
    | .storeCell left right
    | .binary _ left right
    | .letE left right => by simp [Expr.rename, Expr.rename_id left, Expr.rename_id right]
    | .first operand
    | .second operand
    | .loadCell operand
    | .unary _ operand => by simp [Expr.rename, Expr.rename_id operand]
    | .lambda _ _ body => by simp [Expr.rename, Expr.rename_id body]
    | .inLeft _ payload
    | .inRight _ payload
    | .newCell _ payload
    | .construct _ payload => by simp [Expr.rename, Expr.rename_id payload]
    | .caseE scrutinee leftBranch rightBranch
    | .ifE scrutinee leftBranch rightBranch => by
        simp [Expr.rename, Expr.rename_id scrutinee, Expr.rename_id leftBranch,
          Expr.rename_id rightBranch]
    | .ternary _ firstExpr secondExpr thirdExpr => by
        simp [Expr.rename, Expr.rename_id firstExpr, Expr.rename_id secondExpr,
          Expr.rename_id thirdExpr]
    | .matchData _ _ scrutinee branches => by
        simp [Expr.rename, Expr.rename_id scrutinee, Expr.renameList_id branches]

  @[simp] theorem Expr.renameList_id : ∀ expressions : List Expr,
      Expr.renameList expressions Renaming.id = expressions
    | [] => rfl
    | expression :: rest => by
        simp [Expr.renameList, Expr.rename_id expression, Expr.renameList_id rest]

end

mutual

  theorem Expr.rename_comp : ∀ (expr : Expr) (outer inner : Renaming),
      (expr.rename inner).rename outer = expr.rename (outer.comp inner)
    | .unit, _, _ | .bool _, _, _ | .word _, _, _ | .var _, _, _ => rfl
    | .pair left right, outer, inner
    | .apply left right, outer, inner
    | .storeCell left right, outer, inner
    | .binary _ left right, outer, inner
    | .letE left right, outer, inner => by
        simp [Expr.rename, Expr.rename_comp left, Expr.rename_comp right]
    | .first operand, outer, inner
    | .second operand, outer, inner
    | .loadCell operand, outer, inner
    | .unary _ operand, outer, inner => by
        simp [Expr.rename, Expr.rename_comp operand]
    | .lambda _ _ body, outer, inner => by
        simp [Expr.rename, Expr.rename_comp body]
    | .inLeft _ payload, outer, inner
    | .inRight _ payload, outer, inner
    | .newCell _ payload, outer, inner
    | .construct _ payload, outer, inner => by
        simp [Expr.rename, Expr.rename_comp payload]
    | .caseE scrutinee leftBranch rightBranch, outer, inner
    | .ifE scrutinee leftBranch rightBranch, outer, inner => by
        simp [Expr.rename, Expr.rename_comp scrutinee,
          Expr.rename_comp leftBranch, Expr.rename_comp rightBranch]
    | .ternary _ firstExpr secondExpr thirdExpr, outer, inner => by
        simp [Expr.rename, Expr.rename_comp firstExpr, Expr.rename_comp secondExpr,
          Expr.rename_comp thirdExpr]
    | .matchData _ _ scrutinee branches, outer, inner => by
        simp [Expr.rename, Expr.rename_comp scrutinee,
          Expr.renameList_comp branches]

  theorem Expr.renameList_comp : ∀
      (expressions : List Expr) (outer inner : Renaming),
      Expr.renameList (Expr.renameList expressions inner) outer =
        Expr.renameList expressions (outer.comp inner)
    | [], _, _ => rfl
    | expression :: rest, outer, inner => by
        simp [Expr.renameList, Expr.rename_comp expression,
          Expr.renameList_comp rest]

end


mutual

  @[simp] theorem Expr.rename_insertion : ∀ (expr : Expr) (cutoff : Nat),
      expr.rename (Renaming.insertion cutoff) = expr.weakenAt cutoff
    | .unit, _ => by simp [Expr.rename, Expr.weakenAt]
    | .bool _, _ => by simp [Expr.rename, Expr.weakenAt]
    | .word _, _ => by simp [Expr.rename, Expr.weakenAt]
    | .var index, cutoff => by
        by_cases shifted : cutoff ≤ index <;>
          simp [Expr.rename, Expr.weakenAt, Renaming.insertion, shifted]
    | .pair left right, cutoff
    | .apply left right, cutoff
    | .storeCell left right, cutoff
    | .binary _ left right, cutoff
    | .letE left right, cutoff => by
        simp [Expr.rename, Expr.weakenAt, Expr.rename_insertion left,
          Expr.rename_insertion right]
    | .first operand, cutoff
    | .second operand, cutoff
    | .loadCell operand, cutoff
    | .unary _ operand, cutoff => by
        simp [Expr.rename, Expr.weakenAt, Expr.rename_insertion operand]
    | .lambda _ _ body, cutoff => by
        simp [Expr.rename, Expr.weakenAt, Expr.rename_insertion body]
    | .inLeft _ payload, cutoff
    | .inRight _ payload, cutoff
    | .newCell _ payload, cutoff
    | .construct _ payload, cutoff => by
        simp [Expr.rename, Expr.weakenAt, Expr.rename_insertion payload]
    | .caseE scrutinee leftBranch rightBranch, cutoff
    | .ifE scrutinee leftBranch rightBranch, cutoff => by
        simp [Expr.rename, Expr.weakenAt, Expr.rename_insertion scrutinee,
          Expr.rename_insertion leftBranch, Expr.rename_insertion rightBranch]
    | .ternary _ firstExpr secondExpr thirdExpr, cutoff => by
        simp [Expr.rename, Expr.weakenAt, Expr.rename_insertion firstExpr,
          Expr.rename_insertion secondExpr, Expr.rename_insertion thirdExpr]
    | .matchData _ _ scrutinee branches, cutoff => by
        simp [Expr.rename, Expr.weakenAt, Expr.rename_insertion scrutinee,
          Expr.renameList_insertion branches]

  theorem Expr.renameList_insertion : ∀
      (expressions : List Expr) (cutoff : Nat),
      Expr.renameList expressions (Renaming.insertion cutoff) =
        expressions.map fun expression => expression.weakenAt cutoff
    | [], _ => rfl
    | expression :: rest, cutoff => by
        simp [Expr.renameList, Expr.rename_insertion expression,
          Expr.renameList_insertion rest]

end

end Solcore.Core

/-!
## Consolidated module: `Solcore.Core.Renaming`
-/

set_option autoImplicit false

namespace Solcore.Core

namespace Context

def insertAt : Context → Nat → Ty → Context
  | context, 0, type => type :: context
  | [], _ + 1, type => [type]
  | head :: tail, cutoff + 1, type => head :: insertAt tail cutoff type

end Context

namespace Renaming

def Respects (mapping : Renaming) (source target : Context) : Prop :=
  ∀ ⦃index type⦄, source[index]? = some type →
    target[mapping index]? = some type

@[simp] theorem respects_id (context : Context) :
    Respects id context context := by
  intro index type found
  exact found

theorem Respects.comp
    {inner outer : Renaming} {first second third : Context}
    (outerRespect : Respects outer second third)
    (innerRespect : Respects inner first second) :
    Respects (comp outer inner) first third := by
  intro index type found
  exact outerRespect (innerRespect found)

theorem Respects.lift
    {mapping : Renaming} {source target : Context}
    (respect : Respects mapping source target)
    (binder : Ty) :
    Respects mapping.lift (binder :: source) (binder :: target) := by
  intro index type found
  cases index with
  | zero => simpa [Renaming.lift] using found
  | succ index =>
      simp [Renaming.lift] at found ⊢
      exact respect found

theorem insertion_respects_insertAt
    (source : Context) (cutoff : Nat) (inserted : Ty) :
    Respects (insertion cutoff) source (source.insertAt cutoff inserted) := by
  induction cutoff generalizing source with
  | zero =>
      intro index type found
      simpa [insertion, Context.insertAt] using found
  | succ cutoff inductionHypothesis =>
      cases source with
      | nil =>
          intro index type found
          simp at found
      | cons head tail =>
          rw [← lift_insertion cutoff]
          exact (inductionHypothesis tail).lift head

end Renaming

theorem HasType.rename
    {context : Context} {expr : Expr} {type : Ty}
    {definitions : DataEnvironment}
    (typing : HasType context expr type definitions)
    {target : Context} {mapping : Renaming}
    (respect : mapping.Respects context target) :
    HasType target (expr.rename mapping) type definitions := by
  induction typing using HasType.rec
      (motive_2 := fun context resultType payloadTypes branches definitions _ =>
        ∀ {target : Context} {mapping : Renaming},
          mapping.Respects context target →
          BranchesHaveType target resultType payloadTypes
            (Expr.renameList branches mapping.lift) definitions)
      generalizing target mapping with
  | unit => exact .unit
  | bool => exact .bool
  | word => exact .word
  | var found => exact .var (respect found)
  | pair _ _ leftIH rightIH => exact .pair (leftIH respect) (rightIH respect)
  | first _ operandIH => exact .first (operandIH respect)
  | second _ operandIH => exact .second (operandIH respect)
  | lambda parameterWellFormed resultWellFormed _ bodyIH =>
      exact .lambda parameterWellFormed resultWellFormed
        (bodyIH (respect.lift _))
  | apply _ _ functionIH argumentIH =>
      exact .apply (functionIH respect) (argumentIH respect)
  | inLeft annotationWellFormed _ payloadIH =>
      exact .inLeft annotationWellFormed (payloadIH respect)
  | inRight annotationWellFormed _ payloadIH =>
      exact .inRight annotationWellFormed (payloadIH respect)
  | caseE _ _ _ scrutineeIH leftIH rightIH =>
      exact .caseE (scrutineeIH respect)
        (leftIH (respect.lift _)) (rightIH (respect.lift _))
  | newCell _ payload initializerIH =>
      exact .newCell (initializerIH respect) payload
  | loadCell _ payload referenceIH =>
      exact .loadCell (referenceIH respect) payload
  | storeCell _ _ payload referenceIH valueIH =>
      exact .storeCell (referenceIH respect) (valueIH respect) payload
  | construct found _ payloadIH =>
      exact .construct found (payloadIH respect)
  | matchData found resultWellFormed _ _ scrutineeIH branchesIH =>
      exact .matchData found resultWellFormed
        (scrutineeIH respect) (branchesIH respect)
  | unary _ operandIH => exact .unary (operandIH respect)
  | binary _ _ leftIH rightIH => exact .binary (leftIH respect) (rightIH respect)
  | ternary _ _ _ firstIH secondIH thirdIH =>
      exact .ternary (firstIH respect) (secondIH respect) (thirdIH respect)
  | letE _ _ valueIH bodyIH =>
      exact .letE (valueIH respect) (bodyIH (respect.lift _))
  | ifE _ _ _ conditionIH thenIH elseIH =>
      exact .ifE (conditionIH respect) (thenIH respect) (elseIH respect)
  | nil => exact BranchesHaveType.nil
  | cons _ _ branchIH branchesIH =>
      apply BranchesHaveType.cons
      · apply branchIH
        exact Renaming.Respects.lift (by assumption) _
      · apply branchesIH
        assumption

theorem BranchesHaveType.rename
    {context : Context} {resultType : Ty} {payloadTypes : List Ty}
    {branches : List Expr} {definitions : DataEnvironment}
    (typing : BranchesHaveType context resultType payloadTypes branches definitions)
    {target : Context} {mapping : Renaming}
    (respect : mapping.Respects context target) :
    BranchesHaveType target resultType payloadTypes
      (Expr.renameList branches mapping.lift) definitions :=
  by
    induction payloadTypes generalizing branches with
    | nil =>
        cases typing
        exact BranchesHaveType.nil
    | cons payloadType payloadTypes inductionHypothesis =>
        cases typing with
        | cons branchTyping branchesTyping =>
            exact BranchesHaveType.cons
              (branchTyping.rename (respect.lift _))
              (inductionHypothesis branchesTyping)


theorem HasType.weakenAt
    {context : Context} {expr : Expr} {type inserted : Ty}
    {definitions : DataEnvironment}
    (typing : HasType context expr type definitions)
    (cutoff : Nat) :
    HasType (context.insertAt cutoff inserted)
      (expr.weakenAt cutoff) type definitions := by
  rw [← Expr.rename_insertion]
  exact typing.rename (Renaming.insertion_respects_insertAt context cutoff inserted)

theorem infer_rename
    {context target : Context} {expr : Expr} {type : Ty}
    {definitions : DataEnvironment} {mapping : Renaming}
    (inferred : infer? context expr definitions = some type)
    (respect : mapping.Respects context target) :
    infer? target (expr.rename mapping) definitions = some type :=
  infer_complete ((infer_sound inferred).rename respect)

end Solcore.Core

/-!
## Consolidated module: `Solcore.Core.RenamingRuntime`
-/

set_option autoImplicit false

namespace Solcore.Core

mutual

  inductive ValuesRelated : Value → Value → Prop where
    | unit : ValuesRelated .unit .unit
    | bool (value : Bool) : ValuesRelated (.bool value) (.bool value)
    | word (value : Word) : ValuesRelated (.word value) (.word value)
    | hostFunction (function : HostFunction) :
        ValuesRelated (.hostFunction function) (.hostFunction function)
    | pair {left left' right right' : Value} :
        ValuesRelated left left' → ValuesRelated right right' →
        ValuesRelated (.pair left right) (.pair left' right')
    | closure
        {parameterType resultType : Ty} {body : Expr}
        {environment environment' : Environment}
        (mapping : Renaming)
        (environments : EnvironmentsRelated mapping environment environment') :
        ValuesRelated
          (.closure parameterType resultType body environment)
          (.closure parameterType resultType
            (body.rename mapping.lift) environment')
    | inLeft {rightType : Ty} {payload payload' : Value} :
        ValuesRelated payload payload' →
        ValuesRelated (.inLeft rightType payload) (.inLeft rightType payload')
    | inRight {leftType : Ty} {payload payload' : Value} :
        ValuesRelated payload payload' →
        ValuesRelated (.inRight leftType payload) (.inRight leftType payload')
    | cellRef {elementType : Ty} {location : Location} :
        ValuesRelated (.cellRef elementType location) (.cellRef elementType location)
    | constructed {constructor : ConstructorId} {payload payload' : Value} :
        ValuesRelated payload payload' →
        ValuesRelated (.constructed constructor payload)
          (.constructed constructor payload')

  inductive EnvironmentsRelated :
      Renaming → Environment → Environment → Prop where
    | intro
        {mapping : Renaming} {source target : Environment}
        (targetBounds : ∀ index, index < source.length →
          mapping index < target.length)
        (values : ∀ (index) (sourceBound : index < source.length),
          ValuesRelated (getElem source index sourceBound)
            (getElem target (mapping index) (targetBounds index sourceBound))) :
        EnvironmentsRelated mapping source target

end

namespace EnvironmentsRelated

theorem lookup
    {mapping : Renaming} {source target : Environment}
    (related : EnvironmentsRelated mapping source target)
    {index : Nat} {value : Value}
    (found : source[index]? = some value) :
    ∃ value', target[mapping index]? = some value' ∧ ValuesRelated value value' := by
  cases related with
  | intro targetBounds values =>
      obtain ⟨sourceBound, valueEquality⟩ :=
        List.getElem?_eq_some_iff.mp found
      subst value
      let targetBound := targetBounds index sourceBound
      exact ⟨target[mapping index],
        List.getElem?_eq_getElem targetBound, values index sourceBound⟩

theorem empty (mapping : Renaming) (target : Environment) :
    EnvironmentsRelated mapping [] target := by
  constructor
  · intro index sourceBound
    simp at sourceBound
  · intro index sourceBound
    simp at sourceBound

theorem extend
    {mapping : Renaming} {source target : Environment}
    (environments : EnvironmentsRelated mapping source target)
    {value value' : Value}
    (values : ValuesRelated value value') :
    EnvironmentsRelated mapping.lift (value :: source) (value' :: target) := by
  cases environments with
  | intro targetBounds relatedValues =>
      constructor
      · intro index sourceBound
        cases index with
        | zero =>
            change ValuesRelated value value'
            exact values
        | succ index =>
            simp [Renaming.lift] at sourceBound ⊢
            exact relatedValues index sourceBound
      · intro index sourceBound
        cases index with
        | zero => simp [Renaming.lift]
        | succ index =>
            simp [Renaming.lift] at sourceBound ⊢
            exact targetBounds index sourceBound

end EnvironmentsRelated

mutual

  theorem ValuesRelated.refl : ∀ value : Value, ValuesRelated value value
    | .unit => .unit
    | .bool value => .bool value
    | .word value => .word value
    | .hostFunction function => .hostFunction function
    | .pair left right =>
        .pair (ValuesRelated.refl left) (ValuesRelated.refl right)
    | .closure parameterType resultType body environment => by
        simpa using ValuesRelated.closure Renaming.id
          (EnvironmentsRelated.refl environment)
    | .inLeft rightType payload => .inLeft (ValuesRelated.refl payload)
    | .inRight leftType payload => .inRight (ValuesRelated.refl payload)
    | .cellRef elementType location => .cellRef
    | .constructed constructor payload =>
        .constructed (ValuesRelated.refl payload)

  theorem EnvironmentsRelated.refl : ∀ environment : Environment,
      EnvironmentsRelated Renaming.id environment environment
    | [] => EnvironmentsRelated.empty Renaming.id []
    | value :: rest => by
        simpa using (EnvironmentsRelated.refl rest).extend (ValuesRelated.refl value)

end

namespace ValuesRelated

theorem unit_iff {target : Value} :
    ValuesRelated .unit target ↔ target = .unit := by
  constructor
  · intro related
    cases related
    rfl
  · rintro rfl
    exact .unit

theorem bool_iff {value : Bool} {target : Value} :
    ValuesRelated (.bool value) target ↔ target = .bool value := by
  constructor
  · intro related
    cases related
    rfl
  · rintro rfl
    exact .bool value

theorem word_iff {value : Word} {target : Value} :
    ValuesRelated (.word value) target ↔ target = .word value := by
  constructor
  · intro related
    cases related
    rfl
  · rintro rfl
    exact .word value

end ValuesRelated

inductive StoresRelated : Store → Store → Prop where
  | nil : StoresRelated [] []
  | cons {value value' : Value} {rest rest' : Store} :
      ValuesRelated value value' → StoresRelated rest rest' →
      StoresRelated (value :: rest) (value' :: rest')

namespace StoresRelated

theorem refl (store : Store) : StoresRelated store store := by
  induction store with
  | nil => exact .nil
  | cons value rest inductionHypothesis =>
      exact .cons (ValuesRelated.refl value) inductionHypothesis

@[simp] theorem length_eq
    {source target : Store} (related : StoresRelated source target) :
    source.length = target.length := by
  induction related with
  | nil => rfl
  | cons _ _ inductionHypothesis => simp [inductionHypothesis]

theorem lookup
    {source target : Store} (related : StoresRelated source target)
    {location : Location} {value : Value}
    (found : source[location]? = some value) :
    ∃ value', target[location]? = some value' ∧ ValuesRelated value value' := by
  induction related generalizing location value with
  | nil => simp at found
  | cons headRelated tailRelated inductionHypothesis =>
      cases location with
      | zero =>
          simp at found
          subst value
          exact ⟨_, by simp, headRelated⟩
      | succ location =>
          simp at found ⊢
          exact inductionHypothesis found

theorem read
    {source target : Store} (related : StoresRelated source target)
    {location : Location} {value : Value}
    (read : source.read? location = some value) :
    ∃ value', target.read? location = some value' ∧ ValuesRelated value value' :=
  related.lookup read

theorem allocate
    {source target : Store} (stores : StoresRelated source target)
    {value value' : Value} (values : ValuesRelated value value') :
    StoresRelated (source.allocate value).1 (target.allocate value').1 ∧
      (source.allocate value).2 = (target.allocate value').2 := by
  constructor
  · simp only [Store.allocate]
    induction stores with
    | nil => exact .cons values .nil
    | cons headRelated tailRelated inductionHypothesis =>
        exact .cons headRelated inductionHypothesis
  · simp [Store.allocate, stores.length_eq]

theorem set
    {source target : Store} (stores : StoresRelated source target)
    {location : Location} {value value' : Value}
    (values : ValuesRelated value value')
    (inBounds : location < source.length) :
    StoresRelated (source.set location value) (target.set location value') := by
  induction stores generalizing location with
  | nil => simp at inBounds
  | cons headRelated tailRelated inductionHypothesis =>
      cases location with
      | zero => exact .cons values tailRelated
      | succ location =>
          simp at inBounds
          exact .cons headRelated (inductionHypothesis inBounds)

theorem write
    {source target updatedSource : Store}
    (stores : StoresRelated source target)
    {location : Location} {value value' : Value}
    (values : ValuesRelated value value')
    (written : source.write? location value = some updatedSource) :
    ∃ updatedTarget,
      target.write? location value' = some updatedTarget ∧
        StoresRelated updatedSource updatedTarget := by
  obtain ⟨sourceBound, rfl⟩ := Store.write?_eq_some_iff.mp written
  have targetBound : location < target.length := by
    rw [← stores.length_eq]
    exact sourceBound
  exact ⟨target.set location value',
    Store.write?_eq_some_iff.mpr ⟨targetBound, rfl⟩,
    stores.set values sourceBound⟩

end StoresRelated

end Solcore.Core

/-!
## Consolidated module: `Solcore.Core.RenamingEval`
-/

set_option autoImplicit false

namespace Solcore.Core

private theorem UnaryOp.apply_related
    {op : UnaryOp} {source target result : Value}
    (values : ValuesRelated source target)
    (applied : op.apply source = some result) :
    ∃ result', op.apply target = some result' ∧ ValuesRelated result result' := by
  cases op <;> cases values <;>
    simp [UnaryOp.apply] at applied ⊢ <;>
    cases applied <;> first | exact .bool _ | exact .word _

private theorem BinaryOp.apply_related
    {op : BinaryOp} {left left' right right' result : Value}
    (leftValues : ValuesRelated left left')
    (rightValues : ValuesRelated right right')
    (applied : op.apply left right = some result) :
    ∃ result',
      op.apply left' right' = some result' ∧ ValuesRelated result result' := by
  cases op <;> cases leftValues <;> cases rightValues <;>
    simp [BinaryOp.apply] at applied ⊢ <;>
    cases applied <;> first | exact .bool _ | exact .word _

private theorem TernaryOp.apply_related
    {op : TernaryOp}
    {firstValue firstValue' secondValue secondValue' thirdValue thirdValue'
      result : Value}
    (firstValues : ValuesRelated firstValue firstValue')
    (secondValues : ValuesRelated secondValue secondValue')
    (thirdValues : ValuesRelated thirdValue thirdValue')
    (applied : op.apply firstValue secondValue thirdValue = some result) :
    ∃ result',
      op.apply firstValue' secondValue' thirdValue' = some result' ∧
      ValuesRelated result result' := by
  cases op <;> cases firstValues <;> cases secondValues <;>
    cases thirdValues <;>
    simp [TernaryOp.apply] at applied ⊢ <;>
    cases applied <;> exact .word _

private theorem Expr.renameList_lookup
    {branches : List Expr} {index : Nat} {branch : Expr}
    (found : branches[index]? = some branch)
    (mapping : Renaming) :
    (Expr.renameList branches mapping)[index]? = some (branch.rename mapping) := by
  induction branches generalizing index with
  | nil => simp at found
  | cons head tail inductionHypothesis =>
      cases index with
      | zero =>
          simp at found
          subst branch
          simp [Expr.renameList]
      | succ index =>
          simp [Expr.renameList] at found ⊢
          exact inductionHypothesis found

theorem Evaluates.rename
    {sourceEnvironment : Environment} {sourceInitialStore : Store}
    {expr : Expr} {sourceValue : Value} {sourceFinalStore : Store}
    (evaluation : Evaluates sourceEnvironment sourceInitialStore expr
      sourceValue sourceFinalStore)
    {mapping : Renaming} {targetEnvironment : Environment}
    {targetInitialStore : Store}
    (environments :
      EnvironmentsRelated mapping sourceEnvironment targetEnvironment)
    (stores : StoresRelated sourceInitialStore targetInitialStore) :
    ∃ targetValue targetFinalStore,
      Evaluates targetEnvironment targetInitialStore (expr.rename mapping)
        targetValue targetFinalStore ∧
      ValuesRelated sourceValue targetValue ∧
      StoresRelated sourceFinalStore targetFinalStore := by
  induction evaluation generalizing mapping targetEnvironment targetInitialStore with
  | unit => exact ⟨.unit, _, .unit, .unit, stores⟩
  | bool => exact ⟨_, _, .bool, .bool _, stores⟩
  | word => exact ⟨_, _, .word, .word _, stores⟩
  | pair _ _ leftIH rightIH =>
      obtain ⟨left', middleStore', leftEvaluation, leftRelated, middleRelated⟩ :=
        leftIH environments stores
      obtain ⟨right', finalStore', rightEvaluation, rightRelated, finalRelated⟩ :=
        rightIH environments middleRelated
      exact ⟨.pair left' right', finalStore',
        .pair leftEvaluation rightEvaluation,
        .pair leftRelated rightRelated, finalRelated⟩
  | first _ operandIH =>
      obtain ⟨operand', finalStore', operandEvaluation, operandRelated,
        finalRelated⟩ := operandIH environments stores
      cases operandRelated with
      | pair leftRelated rightRelated =>
          exact ⟨_, finalStore', .first operandEvaluation,
            leftRelated, finalRelated⟩
  | second _ operandIH =>
      obtain ⟨operand', finalStore', operandEvaluation, operandRelated,
        finalRelated⟩ := operandIH environments stores
      cases operandRelated with
      | pair leftRelated rightRelated =>
          exact ⟨_, finalStore', .second operandEvaluation,
            rightRelated, finalRelated⟩
  | inLeft _ payloadIH =>
      obtain ⟨payload', finalStore', payloadEvaluation, payloadRelated,
        finalRelated⟩ := payloadIH environments stores
      exact ⟨.inLeft _ payload', finalStore', .inLeft payloadEvaluation,
        .inLeft payloadRelated, finalRelated⟩
  | inRight _ payloadIH =>
      obtain ⟨payload', finalStore', payloadEvaluation, payloadRelated,
        finalRelated⟩ := payloadIH environments stores
      exact ⟨.inRight _ payload', finalStore', .inRight payloadEvaluation,
        .inRight payloadRelated, finalRelated⟩
  | caseLeft _ _ scrutineeIH branchIH =>
      obtain ⟨scrutinee', branchStore', scrutineeEvaluation,
        scrutineeRelated, branchStoreRelated⟩ := scrutineeIH environments stores
      cases scrutineeRelated with
      | inLeft payloadRelated =>
          obtain ⟨result', finalStore', branchEvaluation, resultRelated,
            finalRelated⟩ :=
            branchIH (environments.extend payloadRelated) branchStoreRelated
          exact ⟨result', finalStore',
            .caseLeft scrutineeEvaluation branchEvaluation,
            resultRelated, finalRelated⟩
  | caseRight _ _ scrutineeIH branchIH =>
      obtain ⟨scrutinee', branchStore', scrutineeEvaluation,
        scrutineeRelated, branchStoreRelated⟩ := scrutineeIH environments stores
      cases scrutineeRelated with
      | inRight payloadRelated =>
          obtain ⟨result', finalStore', branchEvaluation, resultRelated,
            finalRelated⟩ :=
            branchIH (environments.extend payloadRelated) branchStoreRelated
          exact ⟨result', finalStore',
            .caseRight scrutineeEvaluation branchEvaluation,
            resultRelated, finalRelated⟩
  | lambda =>
      exact ⟨_, _, .lambda, .closure mapping environments, stores⟩
  | apply _ _ _ functionIH argumentIH bodyIH =>
      obtain ⟨function', argumentStore', functionEvaluation, functionRelated,
        argumentStoreRelated⟩ := functionIH environments stores
      cases functionRelated with
      | closure bodyMapping capturedRelated =>
          obtain ⟨argument', bodyStore', argumentEvaluation, argumentRelated,
            bodyStoreRelated⟩ := argumentIH environments argumentStoreRelated
          obtain ⟨result', finalStore', bodyEvaluation, resultRelated,
            finalRelated⟩ :=
            bodyIH (capturedRelated.extend argumentRelated) bodyStoreRelated
          exact ⟨result', finalStore',
            .apply functionEvaluation argumentEvaluation bodyEvaluation,
            resultRelated, finalRelated⟩
  | var found =>
      obtain ⟨value', found', values⟩ := environments.lookup found
      exact ⟨value', targetInitialStore, .var found', values, stores⟩
  | newCell _ initializerIH =>
      obtain ⟨value', initializedStore', initializerEvaluation, values,
        initializedStores⟩ := initializerIH environments stores
      have allocated := initializedStores.allocate values
      rw [Store.allocate_updatedStore, Store.allocate_updatedStore] at allocated
      rw [initializedStores.length_eq]
      exact ⟨.cellRef _ initializedStore'.length,
        initializedStore' ++ [value'], .newCell initializerEvaluation,
        .cellRef, allocated.1⟩
  | loadCell _ read operandIH =>
      obtain ⟨reference', referenceStore', referenceEvaluation,
        referenceRelated, referenceStores⟩ := operandIH environments stores
      cases referenceRelated with
      | cellRef =>
          obtain ⟨value', read', values⟩ := referenceStores.read read
          exact ⟨value', referenceStore', .loadCell referenceEvaluation read',
            values, referenceStores⟩
  | storeCell _ read _ written referenceIH valueIH =>
      obtain ⟨reference', referenceStore', referenceEvaluation,
        referenceRelated, referenceStores⟩ := referenceIH environments stores
      cases referenceRelated with
      | cellRef =>
          obtain ⟨oldValue', read', oldValues⟩ := referenceStores.read read
          obtain ⟨value', valueStore', valueEvaluation, values, valueStores⟩ :=
            valueIH environments referenceStores
          obtain ⟨finalStore', written', finalStores⟩ :=
            valueStores.write values written
          exact ⟨.unit, finalStore',
            .storeCell referenceEvaluation read' valueEvaluation written',
            .unit, finalStores⟩
  | construct _ payloadIH =>
      obtain ⟨payload', finalStore', payloadEvaluation, payloadRelated,
        finalRelated⟩ := payloadIH environments stores
      exact ⟨.constructed _ payload', finalStore',
        .construct payloadEvaluation, .constructed payloadRelated, finalRelated⟩
  | matchData _ owner found _ scrutineeIH branchIH =>
      obtain ⟨scrutinee', branchStore', scrutineeEvaluation,
        scrutineeRelated, branchStores⟩ := scrutineeIH environments stores
      cases scrutineeRelated with
      | constructed payloadRelated =>
          obtain ⟨result', finalStore', branchEvaluation, resultRelated,
            finalRelated⟩ :=
            branchIH (environments.extend payloadRelated) branchStores
          exact ⟨result', finalStore',
            .matchData scrutineeEvaluation owner
              (Expr.renameList_lookup found mapping.lift) branchEvaluation,
            resultRelated, finalRelated⟩
  | unary _ applied operandIH =>
      obtain ⟨operand', finalStore', operandEvaluation, operandRelated,
        finalRelated⟩ := operandIH environments stores
      obtain ⟨result', applied', resultRelated⟩ :=
        UnaryOp.apply_related operandRelated applied
      exact ⟨result', finalStore', .unary operandEvaluation applied',
        resultRelated, finalRelated⟩
  | binary _ _ applied leftIH rightIH =>
      obtain ⟨left', rightStore', leftEvaluation, leftRelated, rightStores⟩ :=
        leftIH environments stores
      obtain ⟨right', finalStore', rightEvaluation, rightRelated,
        finalRelated⟩ := rightIH environments rightStores
      obtain ⟨result', applied', resultRelated⟩ :=
        BinaryOp.apply_related leftRelated rightRelated applied
      exact ⟨result', finalStore',
        .binary leftEvaluation rightEvaluation applied',
        resultRelated, finalRelated⟩
  | ternary _ _ _ applied firstIH secondIH thirdIH =>
      obtain ⟨first', secondStore', firstEvaluation, firstRelated,
        secondStores⟩ := firstIH environments stores
      obtain ⟨second', thirdStore', secondEvaluation, secondRelated,
        thirdStores⟩ := secondIH environments secondStores
      obtain ⟨third', finalStore', thirdEvaluation, thirdRelated,
        finalRelated⟩ := thirdIH environments thirdStores
      obtain ⟨result', applied', resultRelated⟩ :=
        TernaryOp.apply_related firstRelated secondRelated thirdRelated applied
      exact ⟨result', finalStore',
        .ternary firstEvaluation secondEvaluation thirdEvaluation applied',
        resultRelated, finalRelated⟩
  | letE _ _ valueIH bodyIH =>
      obtain ⟨value', bodyStore', valueEvaluation, valueRelated,
        bodyStores⟩ := valueIH environments stores
      obtain ⟨result', finalStore', bodyEvaluation, resultRelated,
        finalRelated⟩ :=
        bodyIH (environments.extend valueRelated) bodyStores
      exact ⟨result', finalStore', .letE valueEvaluation bodyEvaluation,
        resultRelated, finalRelated⟩
  | ifTrue _ _ conditionIH branchIH =>
      obtain ⟨condition', branchStore', conditionEvaluation,
        conditionRelated, branchStores⟩ := conditionIH environments stores
      rw [ValuesRelated.bool_iff.mp conditionRelated] at conditionEvaluation
      obtain ⟨result', finalStore', branchEvaluation, resultRelated,
        finalRelated⟩ := branchIH environments branchStores
      exact ⟨result', finalStore',
        .ifTrue conditionEvaluation branchEvaluation,
        resultRelated, finalRelated⟩
  | ifFalse _ _ conditionIH branchIH =>
      obtain ⟨condition', branchStore', conditionEvaluation,
        conditionRelated, branchStores⟩ := conditionIH environments stores
      rw [ValuesRelated.bool_iff.mp conditionRelated] at conditionEvaluation
      obtain ⟨result', finalStore', branchEvaluation, resultRelated,
        finalRelated⟩ := branchIH environments branchStores
      exact ⟨result', finalStore',
        .ifFalse conditionEvaluation branchEvaluation,
        resultRelated, finalRelated⟩

end Solcore.Core

/-!
## Consolidated module: `Solcore.Core.RenamingSafety`
-/

set_option autoImplicit false

namespace Solcore.Core

theorem ValuesRelated.eq_of_cellPayload
    {type : Ty} {source target : Value} {definitions : DataEnvironment}
    (payload : CellPayload type)
    (typing : ValueHasType source type definitions)
    (related : ValuesRelated source target) :
    source = target := by
  induction payload generalizing source target with
  | unit =>
      cases typing
      exact (ValuesRelated.unit_iff.mp related).symm
  | bool =>
      cases typing
      exact (ValuesRelated.bool_iff.mp related).symm
  | word =>
      cases typing
      exact (ValuesRelated.word_iff.mp related).symm
  | product leftPayload rightPayload leftIH rightIH =>
      cases typing with
      | pair leftTyping rightTyping =>
          cases related with
          | pair leftRelated rightRelated =>
              rw [leftIH leftTyping leftRelated, rightIH rightTyping rightRelated]
  | sum leftPayload rightPayload leftIH rightIH =>
      cases typing with
      | inLeft payloadTyping =>
          cases related with
          | inLeft payloadRelated =>
              rw [leftIH payloadTyping payloadRelated]
      | inRight payloadTyping =>
          cases related with
          | inRight payloadRelated =>
              rw [rightIH payloadTyping payloadRelated]

namespace StoreHasTypes

private theorem tail
    {elementType : Ty} {world : StoreTyping}
    {head : Value} {store : Store}
    (typing : StoreHasTypes (elementType :: world) (head :: store)) :
    StoreHasTypes world store where
  length_eq := by
    simpa using typing.length_eq
  lookup := by
    intro location storedType found
    obtain ⟨value, read, payload, valueTyping⟩ :=
      typing.lookup (location := location + 1) (by simpa using found)
    exact ⟨value, by simpa [Store.read?] using read, payload, valueTyping⟩

end StoreHasTypes

theorem StoresRelated.eq_of_hasTypes
    {world : StoreTyping} {source target : Store}
    (typing : StoreHasTypes world source)
    (related : StoresRelated source target) :
    source = target := by
  induction related generalizing world with
  | nil => rfl
  | cons headRelated tailRelated inductionHypothesis =>
      cases world with
      | nil =>
          have lengthEquality := typing.length_eq
          simp at lengthEquality
      | cons elementType world =>
          obtain ⟨headValue, headRead, payload, headTyping⟩ :=
            typing.lookup (location := 0) (elementType := elementType) (by simp)
          simp [Store.read?] at headRead
          subst headValue
          have headEquality :=
            headRelated.eq_of_cellPayload payload headTyping
          have tailEquality := inductionHypothesis typing.tail
          simp [headEquality, tailEquality]

theorem EnvironmentsRelated.headInsertion
    (inserted : Value) (environment : Environment) :
    EnvironmentsRelated (Renaming.insertion 0)
      environment (inserted :: environment) := by
  constructor
  · intro index sourceBound
    change ValuesRelated environment[index] environment[index]
    exact ValuesRelated.refl _
  · intro index sourceBound
    simpa [Renaming.insertion] using sourceBound

end Solcore.Core

/-!
## Consolidated module: `Solcore.Core.RenamingInsertion`
-/

set_option autoImplicit false

namespace Solcore.Core

/--
Weakening a typed expression at the outermost context position is exact for
cell-payload result types. The inserted runtime value is completely arbitrary:
the original free variables are shifted past it, so no typing assumption on the
new head is required.
-/
theorem Evaluates.weakenAt_zero_cellPayload
    {definitions : DataEnvironment}
    {environment : Environment} {context : Context}
    {initialStore finalStore : Store} {world : StoreTyping}
    {expr : Expr} {result : Value} {type : Ty}
    (evaluation :
      Evaluates environment initialStore expr result finalStore)
    (typing : HasType context expr type definitions)
    (payload : CellPayload type)
    (environmentTyping :
      RuntimeEnvironmentHasTypes world environment context definitions)
    (storeTyping : StoreHasTypes world initialStore)
    (inserted : Value) :
    Evaluates (inserted :: environment) initialStore
      (expr.weakenAt 0) result finalStore := by
  obtain ⟨finalWorld, _, finalStoreTyping, resultTyping⟩ :=
    evaluation_preserves_type evaluation typing environmentTyping storeTyping
  obtain ⟨targetResult, targetFinalStore, targetEvaluation,
      resultRelated, finalStoresRelated⟩ :=
    evaluation.rename
      (EnvironmentsRelated.headInsertion inserted environment)
      (StoresRelated.refl initialStore)
  have resultEquality : result = targetResult :=
    resultRelated.eq_of_cellPayload payload resultTyping.erase
  have storeEquality : finalStore = targetFinalStore :=
    finalStoresRelated.eq_of_hasTypes finalStoreTyping
  subst targetResult
  subst targetFinalStore
  simpa using targetEvaluation

theorem Evaluates.weakenAt_zero_word
    {definitions : DataEnvironment}
    {environment : Environment} {context : Context}
    {initialStore finalStore : Store} {world : StoreTyping}
    {expr : Expr} {result : Word}
    (evaluation :
      Evaluates environment initialStore expr (.word result) finalStore)
    (typing : HasType context expr .word definitions)
    (environmentTyping :
      RuntimeEnvironmentHasTypes world environment context definitions)
    (storeTyping : StoreHasTypes world initialStore)
    (inserted : Value) :
    Evaluates (inserted :: environment) initialStore
      (expr.weakenAt 0) (.word result) finalStore :=
  evaluation.weakenAt_zero_cellPayload typing .word
    environmentTyping storeTyping inserted

end Solcore.Core
