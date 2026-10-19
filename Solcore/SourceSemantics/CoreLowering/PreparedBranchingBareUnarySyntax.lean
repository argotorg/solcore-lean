import Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchTree

/-! Returned lambda bodies keep the original unary grammar until their
prepared body packet supports projected unary updates. Value assignments and
all existing nested control remain available. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.PreparedBranchingBareUnarySyntax
open Core Frontend SourceInference

def Header (items : List ForItemForm) : Prop :=
  ∀ assignment, .assignBitNot assignment ∈ items → assignment.target.projections = []

mutual
inductive Body (source : TypedSource) : List StatementId → Prop where
  | nil : Body source []
  | cons {id node rest} (found : source.lookupStatement? id = some node)
      (head : Form source node.form) (tail : Body source rest) : Body source (id :: rest)
inductive Form (source : TypedSource) : StatementForm → Prop where
  | leaf {form} (allowed : (match form with
      | .assignBitNot _ | .block _ | .ifThen _ _ _ | .whileLoop _ _ | .forLoop _ _ _ _ | .matchWith _ => False
      | _ => True)) : Form source form
  | bitNot {assignment} (bare : assignment.target.projections = []) : Form source (.assignBitNot assignment)
  | block {statements} (inner : Body source statements) : Form source (.block statements)
  | conditional {condition left right} (first : Body source left) (second : Body source (right.getD [])) :
      Form source (.ifThen condition left right)
  | whileLoop {condition statements} (inner : Body source statements) : Form source (.whileLoop condition statements)
  | forLoop {initial condition post statements} (before : Header initial) (after : Header post)
      (inner : Body source statements) : Form source (.forLoop initial condition post statements)
  | matchWith {resolution} (arms : ∀ arm ∈ resolution.cases, Body source arm.body)
      (fallback : Body source (resolution.defaultBody.getD [])) : Form source (.matchWith resolution)
end

def Position (source : TypedSource) : GenericImperativeMatch.Position → Prop
  | .statements _ statements => Body source statements
  | .initializers items _ post statements => Header items ∧ Header post ∧ Body source statements

private def allProof? {α : Type} (predicate : α → Prop)
    (check : (item : α) → Option (PLift (predicate item))) :
    (items : List α) → Option (PLift (∀ item ∈ items, predicate item))
  | [] => some ⟨by intro item member; cases member⟩
  | first :: rest => do
      let ⟨head⟩ ← check first
      let ⟨tail⟩ ← allProof? predicate check rest
      pure ⟨by intro item member; rcases List.mem_cons.mp member with rfl | member
               · exact head
               · exact tail item member⟩

private def header? (items : List ForItemForm) : Option (PLift (Header items)) := do
  let ⟨found⟩ ← allProof? (fun item => ∀ assignment, item = .assignBitNot assignment → assignment.target.projections = [])
    (fun item => by
      cases item with
      | assignBitNot assignment =>
        exact if bare : assignment.target.projections = [] then
          some ⟨by intro actual same; cases same; exact bare⟩ else none
      | letDecl | expression | assignValue => exact some ⟨by intro actual same; cases same⟩) items
  pure ⟨fun assignment member => found _ member assignment rfl⟩

mutual
private def body? (source : TypedSource) : (fuel : Nat) → (statements : List StatementId) → Option (PLift (Body source statements))
  | _, [] => some ⟨.nil⟩
  | 0, _ :: _ => none
  | fuel + 1, id :: rest => do
      match found : source.lookupStatement? id with
      | none => none
      | some node =>
        let ⟨head⟩ ← form? source fuel node.form
        let ⟨tail⟩ ← body? source fuel rest
        pure ⟨.cons found head tail⟩
private def form? (source : TypedSource) : (fuel : Nat) → (form : StatementForm) → Option (PLift (Form source form))
  | 0, _ => none
  | fuel + 1, form => by
      cases form with
      | assignBitNot assignment =>
        exact if bare : assignment.target.projections = [] then some ⟨.bitNot bare⟩ else none
      | block statements => exact do
        let ⟨inner⟩ ← body? source fuel statements
        pure ⟨.block inner⟩
      | ifThen condition left right => exact do
        let ⟨first⟩ ← body? source fuel left
        let ⟨second⟩ ← body? source fuel (right.getD [])
        pure ⟨.conditional first second⟩
      | whileLoop condition statements => exact do
        let ⟨inner⟩ ← body? source fuel statements
        pure ⟨.whileLoop inner⟩
      | forLoop initial condition post statements => exact do
        let ⟨before⟩ ← header? initial
        let ⟨after⟩ ← header? post
        let ⟨inner⟩ ← body? source fuel statements
        pure ⟨.forLoop before after inner⟩
      | matchWith resolution => exact do
        let ⟨arms⟩ ← allProof? (fun arm : TypedMatchCase => Body source arm.body)
          (fun arm => body? source fuel arm.body) resolution.cases
        let ⟨fallback⟩ ← body? source fuel (resolution.defaultBody.getD [])
        pure ⟨.matchWith arms fallback⟩
      | returnStmt | letDecl | expression | breakStmt | continueStmt | assignValue => exact some ⟨.leaf True.intro⟩
end

def check (source : TypedSource) (statements : List StatementId) : Option (PLift (Body source statements)) :=
  body? source (2 * (source.nodes.length + 1)) statements

theorem Header.tail {item rest} (header : Header (item :: rest)) : Header rest :=
  fun assignment member => header assignment (List.mem_cons_of_mem item member)

theorem Body.tail {source id rest} (body : Body source (id :: rest)) : Body source rest := by
  cases body with | cons _ _ tail => exact tail

theorem Body.head {source id node rest} (body : Body source (id :: rest))
    (found : source.lookupStatement? id = some node) : Form source node.form := by
  cases body with
  | cons actual head tail =>
    cases Option.some.inj (actual.symm.trans found)
    exact head

theorem Body.unary {source id node assignment rest} (body : Body source (id :: rest))
    (found : source.lookupStatement? id = some node) (form : node.form = .assignBitNot assignment) :
    assignment.target.projections = [] := by
  have head := body.head found
  rw [form] at head
  cases head with
  | leaf impossible => cases impossible
  | bitNot bare => exact bare

theorem Body.block {source id node statements rest} (body : Body source (id :: rest))
    (found : source.lookupStatement? id = some node) (form : node.form = .block statements) : Body source statements := by
  have head := body.head found
  rw [form] at head
  cases head with
  | leaf impossible => cases impossible
  | block inner => exact inner

theorem Body.branches {source id node condition left right rest} (body : Body source (id :: rest))
    (found : source.lookupStatement? id = some node) (form : node.form = .ifThen condition left right) :
    Body source left ∧ Body source (right.getD []) := by
  have head := body.head found
  rw [form] at head
  cases head with
  | leaf impossible => cases impossible
  | conditional first second => exact ⟨first, second⟩

theorem Body.loop {source id node condition statements rest} (body : Body source (id :: rest))
    (found : source.lookupStatement? id = some node) (form : node.form = .whileLoop condition statements) : Body source statements := by
  have head := body.head found
  rw [form] at head
  cases head with
  | leaf impossible => cases impossible
  | whileLoop inner => exact inner

theorem Body.for_children {source id node initial condition post statements rest} (body : Body source (id :: rest))
    (found : source.lookupStatement? id = some node) (form : node.form = .forLoop initial condition post statements) :
    Header initial ∧ Header post ∧ Body source statements := by
  have head := body.head found
  rw [form] at head
  cases head with
  | leaf impossible => cases impossible
  | forLoop before after inner => exact ⟨before, after, inner⟩

theorem Body.match_request {source id node resolution rest parent type request childContext}
    (body : Body source (id :: rest)) (found : source.lookupStatement? id = some node)
    (form : node.form = .matchWith resolution)
    (context : GenericMatchChildren.ContextFor source parent type resolution.cases resolution.defaultBody request childContext) :
    Body source request.statements := by
  have head := body.head found
  rw [form] at head
  cases head with
  | leaf impossible => cases impossible
  | matchWith arms fallback =>
    cases context with
    | arm member statements _ _ => rw [statements]; exact arms _ member
    | default statements => simpa only [statements, Option.getD_some] using fallback

end Solcore.SourceSemantics.CoreLowering.PreparedBranchingBareUnarySyntax

namespace Solcore.SourceSemantics.CoreLowering
open Core Frontend SourceInference
open PreparedBranchingBareUnarySyntax

theorem GenericForHeader.PreparedSyntax.bareUnary {source : TypedSource} {approved : ExpressionId → Prop}
    {context : SourceSemantics.Context} {items : List ForItemForm}
    (tree : GenericForHeader.PreparedSyntax source approved context items) (shape : Header items) :
    GenericForHeader.Syntax source approved context items := by
  revert shape
  induction tree with
  | nil => intro _; exact .nil
  | uninitialized declaration mono extended ordinary remaining ih =>
    intro shape
    exact .uninitialized declaration mono extended ordinary (ih shape.tail)
  | initialized declaration mono extended ordinary found sourceType typed syntaxTree remaining ih =>
    intro shape
    exact .initialized declaration mono extended ordinary found sourceType typed syntaxTree (ih shape.tail)
  | discard found typed syntaxTree remaining ih =>
    intro shape
    exact .discard found typed syntaxTree (ih shape.tail)
  | assign sourceTyped writable rightTyped profile children remaining ih =>
    intro shape
    exact .assign sourceTyped writable rightTyped profile children (ih shape.tail)
  | bitNot writable bare profile remaining ih =>
    intro shape
    exact .bitNot writable bare profile (ih shape.tail)
  | bitNotProjected _ _ projected _ _ _ _ =>
    intro shape
    exact False.elim (projected (shape _ List.mem_cons_self))

theorem GenericImperativeMatch.PreparedSyntax.bareUnary {source : TypedSource} {approved : ExpressionId → Prop}
    {context : SourceSemantics.Context} {position : GenericImperativeMatch.Position} {expected : TypeSystem.Ty}
    (tree : GenericImperativeMatch.PreparedSyntax source approved context position expected)
    (shape : PreparedBranchingBareUnarySyntax.Position source position) : GenericImperativeMatch.Syntax source approved context position expected := by
  revert shape
  induction tree with
  | body syntaxTree => intro _; exact .body syntaxTree
  | uninitialized found form declaration mono extended ordinary remaining ih =>
    intro shape
    exact .uninitialized found form declaration mono extended ordinary (ih shape.tail)
  | initialized found form declaration mono extended ordinary initializerFound sourceType typed syntaxTree remaining ih =>
    intro shape
    exact .initialized found form declaration mono extended ordinary initializerFound sourceType typed syntaxTree (ih shape.tail)
  | discard found form notTail sourceType expressionFound typed syntaxTree remaining ih =>
    intro shape
    exact .discard found form notTail sourceType expressionFound typed syntaxTree (ih shape.tail)
  | block found form sourceType inner remaining innerIH restIH =>
    intro shape
    exact .block found form sourceType (innerIH (shape.block found form)) (restIH shape.tail)
  | ifThen found form sourceType conditionFound conditionType typed syntaxTree left right remaining leftIH rightIH restIH =>
    intro shape
    exact .ifThen found form sourceType conditionFound conditionType typed syntaxTree
      (leftIH (shape.branches found form).1) (rightIH (shape.branches found form).2) (restIH shape.tail)
  | breaking found form => intro _; exact .breaking found form
  | continuing found form => intro _; exact .continuing found form
  | whileLoop found form conditionFound conditionType typed syntaxTree inner remaining innerIH restIH =>
    intro shape
    exact .whileLoop found form conditionFound conditionType typed syntaxTree
      (innerIH (shape.loop found form)) (restIH shape.tail)
  | assign found form sourceTyped writable rightTyped profile children remaining ih =>
    intro shape
    exact .assign found form sourceTyped writable rightTyped profile children (ih shape.tail)
  | forLoop found form sourceType initial remaining initialIH restIH =>
    intro shape
    have parts := shape.for_children found form
    exact .forLoop found form sourceType (initialIH parts) (restIH shape.tail)
  | initializersDone found sourceType typed syntaxTree loop post ih =>
    intro shape
    exact .initializersDone found sourceType typed syntaxTree (ih shape.2.2) (post.bareUnary shape.2.1)
  | initializerUninitialized declaration mono extended ordinary remaining ih =>
    intro shape
    exact .initializerUninitialized declaration mono extended ordinary (ih ⟨shape.1.tail, shape.2⟩)
  | initializerInitialized declaration mono extended ordinary found sourceType typed syntaxTree remaining ih =>
    intro shape
    exact .initializerInitialized declaration mono extended ordinary found sourceType typed syntaxTree (ih ⟨shape.1.tail, shape.2⟩)
  | initializerDiscard found typed syntaxTree remaining ih =>
    intro shape
    exact .initializerDiscard found typed syntaxTree (ih ⟨shape.1.tail, shape.2⟩)
  | initializerAssign sourceTyped writable rightTyped profile children remaining ih =>
    intro shape
    exact .initializerAssign sourceTyped writable rightTyped profile children (ih ⟨shape.1.tail, shape.2⟩)
  | bitNot found form writable bare profile remaining ih =>
    intro shape
    exact .bitNot found form writable bare profile (ih shape.tail)
  | bitNotProjected found form _ _ projected _ _ _ _ =>
    intro shape
    exact False.elim (projected (shape.unary found form))
  | initializerBitNot writable bare profile remaining ih =>
    intro shape
    exact .initializerBitNot writable bare profile (ih ⟨shape.1.tail, shape.2⟩)
  | initializerBitNotProjected _ _ projected _ _ _ _ =>
    intro shape
    exact False.elim (projected (shape.1 _ List.mem_cons_self))
  | matchWith found form sourceType scrutineeFound scrutineeTyped scrutineeSyntax casesTyped defaultTyped hidden arms children remaining childrenIH restIH =>
    intro shape
    exact .matchWith found form sourceType scrutineeFound scrutineeTyped scrutineeSyntax casesTyped defaultTyped hidden arms
      (fun request childContext valid => childrenIH request childContext valid (shape.match_request found form valid))
      (restIH shape.tail)
  | terminalBlock unique found form sourceType inner stops ih =>
    intro shape
    exact .terminalBlock unique found form sourceType (ih (shape.block found form)) stops
  | terminalIf unique found form sourceType conditionFound conditionType typed syntaxTree left right leftStops rightStops leftIH rightIH =>
    intro shape
    exact .terminalIf unique found form sourceType conditionFound conditionType typed syntaxTree
      (leftIH (shape.branches found form).1) (rightIH (shape.branches found form).2) leftStops rightStops
  | terminalMatch unique found form sourceType scrutineeFound scrutineeTyped scrutineeSyntax casesTyped defaultTyped hidden arms children stops childrenIH =>
    intro shape
    exact .terminalMatch unique found form sourceType scrutineeFound scrutineeTyped scrutineeSyntax casesTyped defaultTyped hidden arms
      (fun request childContext valid => childrenIH request childContext valid (shape.match_request found form valid)) stops
  | scopedBlock found form inner remaining innerIH restIH =>
    intro shape
    exact .scopedBlock found form (innerIH (shape.block found form)) (restIH shape.tail)

end Solcore.SourceSemantics.CoreLowering
