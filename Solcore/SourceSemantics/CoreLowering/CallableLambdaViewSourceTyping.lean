import Solcore.SourceSemantics.CoreLowering.CallableLambdaBodyReachability
import Solcore.SourceSemantics.CoreLowering.BuiltinLexicalStatements

/-! Independent source typing and lexical syntax across a local lambda view.
Complete reached expression nodes are preserved; owner, inputs and statements
come from the actual metadata receipt. The ordinary builtin expression grammar
closes the recursive typing obligations. No runtime meaning or compiler
equation is assumed, and edited reachable headers are explicitly excluded. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableLambdaViewSourceTyping
open Frontend SourceInference
open CallableLambdaViewEdits CallableLambdaBodyReachability

private def BodyFree : ExpressionForm → Prop
  | .lambda _ _ _ => False
  | .call _ _ (.declaration _) => False
  | .call _ _ (.indirect _) => False
  | _ => True

private def typingChildren : ExpressionForm → List ExpressionId
  | .group inner => [inner]
  | .tuple ids => ids
  | .unary _ operand => [operand]
  | .binary first _ second => [first, second]
  | .conditional condition first second => [condition, first, second]
  | .call _ arguments (.builtinFunction _) => arguments
  | .constructor _ arguments => arguments
  | .member base _ _ => [base]
  | .index base key => [base, key]
  | _ => []

private theorem atomic_free {form : ExpressionForm} (atomic : CompatibleExpressionLiterals.Atomic form) :
    BodyFree form := by cases atomic <;> trivial
private theorem atomic_children {form : ExpressionForm} (atomic : CompatibleExpressionLiterals.Atomic form) :
    typingChildren form = [] := by cases atomic <;> rfl

private def TypedAt (source view : TypedSource) (id : ExpressionId) : Prop :=
  ∀ context type, ExpressionHasType source context id type → ExpressionHasType view context id type

private theorem types {source view : TypedSource} {context : Context}
    {ids : List ExpressionId} {result : List TypeSystem.Ty}
    (children : ∀ id ∈ ids, TypedAt source view id)
    (typed : ExpressionsHaveTypes source context ids result) :
    ExpressionsHaveTypes view context ids result := by
  cases typed with
  | nil => exact .nil _
  | @cons context id ids type result head tail =>
    exact .cons (children id (by simp) _ _ head)
      (types (fun id member => children id (List.mem_cons_of_mem _ member)) tail)
termination_by ids.length

variable {source view : TypedSource} {roots : List NodeId} {changed : List ExpressionId}
  (edited : LocalView source view changed) (avoids : Avoids source roots changed)
  (unique : NodeOccurrencesUnique source)

include edited avoids unique in
private theorem step {id : ExpressionId} {node : ExpressionNode}
    (reached : Reaches source roots (.expression id))
    (found : source.lookupExpression? id = some node) (ordinary : BodyFree node.form)
    (children : ∀ child ∈ typingChildren node.form, TypedAt source view child) :
    TypedAt source view id := by
  intro context type typed
  cases typed with
  | @intro _ _ selected raw plan contains formType rawType rawWellFormed typeWellFormed requirements =>
    have same : selected = node := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
    subst selected
    apply ExpressionHasType.intro
      (lookupExpression?_sound ((expression_lookup edited avoids reached).symm.trans found))
      ?_ rawType rawWellFormed typeWellFormed requirements
    generalize shape : node.form = form at formType children ordinary ⊢
    revert children ordinary
    cases formType with
    | literal valid => intros; exact .literal valid
    | integerLiteral valid => intros; exact .integerLiteral valid
    | reference valid => intros; exact .reference valid
    | group typed => intro children _; exact .group (children _ (by simp [typingChildren]) _ _ typed)
    | tuple typed => intro children _; exact .tuple (types (by simpa only [typingChildren] using children) typed)
    | unary typed operator => intro children _; exact .unary (children _ (by simp [typingChildren]) _ _ typed) operator
    | binary first second operator =>
      intro children _
      exact .binary (children _ (by simp [typingChildren]) _ _ first)
        (children _ (by simp [typingChildren]) _ _ second) operator
    | conditional condition first second =>
      intro children _
      exact .conditional (children _ (by simp [typingChildren]) _ _ condition)
        (children _ (by simp [typingChildren]) _ _ first)
        (children _ (by simp [typingChildren]) _ _ second)
    | lambda => intro _ ordinary; cases ordinary
    | directCall => intro _ ordinary; cases ordinary
    | @builtinCall _ callee arguments function calleeValid typed =>
      intro children _
      have calleeReached : Reaches source roots (.expression callee) :=
        .expression reached found (by simp [shape, ExpressionForm.references])
      cases calleeValid with
      | intro contains form sameType sameRequirements sameCoercions =>
        exact .builtinCall
          (.intro (lookupExpression?_sound ((expression_lookup edited avoids calleeReached).symm.trans
            (lookupExpression?_complete unique contains))) form sameType sameRequirements sameCoercions)
          (types (by simpa only [typingChildren] using children) typed)
    | indirectCall => intro _ ordinary; cases ordinary
    | constructor valid typed =>
      intro children _
      exact .constructor valid (types (by simpa only [typingChildren] using children) typed)
    | member typed selected => intro children _; exact .member (children _ (by simp [typingChildren]) _ _ typed) selected
    | proxy admitted => intros; exact .proxy admitted
    | index base key =>
      intro children _
      exact .index (children _ (by simp [typingChildren]) _ _ base)
        (children _ (by simp [typingChildren]) _ _ key)


include edited avoids unique in
private theorem products {id : ExpressionId} (syntaxTree : CompatibleExpressionProducts.Syntax source id)
    (reached : Reaches source roots (.expression id)) :
    CompatibleExpressionProducts.Syntax view id ∧ TypedAt source view id := by
  induction syntaxTree with
  | literal found atomic =>
    refine ⟨.literal ((expression_lookup edited avoids reached).symm.trans found) atomic, step edited avoids unique reached found ?_ ?_⟩
    · exact atomic_free atomic
    · simp [atomic_children atomic]
  | read found form =>
    refine ⟨.read ((expression_lookup edited avoids reached).symm.trans found) form, step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · simp [form, typingChildren]
  | @group id node inner found form child ih =>
    have childReached : Reaches source roots (.expression inner) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    obtain ⟨certified, typed⟩ := ih childReached
    refine ⟨.group ((expression_lookup edited avoids reached).symm.trans found) form certified, step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren, List.mem_singleton] at member
      subst child
      exact typed
  | @pair id node left right found form first second firstIH secondIH =>
    have firstReached : Reaches source roots (.expression left) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    have secondReached : Reaches source roots (.expression right) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    obtain ⟨firstSyntax, firstTyped⟩ := firstIH firstReached
    obtain ⟨secondSyntax, secondTyped⟩ := secondIH secondReached
    refine ⟨.pair ((expression_lookup edited avoids reached).symm.trans found) form firstSyntax secondSyntax, step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact firstTyped
      · exact secondTyped

include edited avoids unique in
private theorem primitives {id : ExpressionId} (syntaxTree : CompatibleExpressionPrimitives.Syntax source id)
    (reached : Reaches source roots (.expression id)) :
    CompatibleExpressionPrimitives.Syntax view id ∧ TypedAt source view id := by
  induction syntaxTree with
  | product child =>
    obtain ⟨certified, typed⟩ := products edited avoids unique child reached
    exact ⟨.product certified, typed⟩
  | @group id node inner found form child ih =>
    have childReached : Reaches source roots (.expression inner) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    obtain ⟨certified, typed⟩ := ih childReached
    refine ⟨.group ((expression_lookup edited avoids reached).symm.trans found) form certified, step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren, List.mem_singleton] at member
      subst child
      exact typed
  | @pair id node left right found form first second firstIH secondIH =>
    have firstReached : Reaches source roots (.expression left) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    have secondReached : Reaches source roots (.expression right) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    obtain ⟨firstSyntax, firstTyped⟩ := firstIH firstReached
    obtain ⟨secondSyntax, secondTyped⟩ := secondIH secondReached
    refine ⟨.pair ((expression_lookup edited avoids reached).symm.trans found) form firstSyntax secondSyntax, step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact firstTyped
      · exact secondTyped
  | @unary id node operand operator found form child ih =>
    have childReached : Reaches source roots (.expression operand) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    obtain ⟨certified, typed⟩ := ih childReached
    refine ⟨.unary ((expression_lookup edited avoids reached).symm.trans found) form certified, step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren, List.mem_singleton] at member
      subst child
      exact typed
  | @binary id node left right operator found form first second firstIH secondIH =>
    have firstReached : Reaches source roots (.expression left) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    have secondReached : Reaches source roots (.expression right) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    obtain ⟨firstSyntax, firstTyped⟩ := firstIH firstReached
    obtain ⟨secondSyntax, secondTyped⟩ := secondIH secondReached
    refine ⟨.binary ((expression_lookup edited avoids reached).symm.trans found) form firstSyntax secondSyntax, step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact firstTyped
      · exact secondTyped

include edited avoids unique in
private theorem conditionals {id : ExpressionId} (syntaxTree : CompatibleExpressionConditionals.Syntax source id)
    (reached : Reaches source roots (.expression id)) :
    CompatibleExpressionConditionals.Syntax view id ∧ TypedAt source view id := by
  induction syntaxTree with
  | primitive child =>
    obtain ⟨certified, typed⟩ := primitives edited avoids unique child reached
    exact ⟨.primitive certified, typed⟩
  | @group id node inner found form child ih =>
    have childReached : Reaches source roots (.expression inner) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    obtain ⟨certified, typed⟩ := ih childReached
    refine ⟨.group ((expression_lookup edited avoids reached).symm.trans found) form certified, step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren, List.mem_singleton] at member
      subst child
      exact typed
  | @pair id node left right found form first second firstIH secondIH =>
    have firstReached : Reaches source roots (.expression left) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    have secondReached : Reaches source roots (.expression right) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    obtain ⟨firstSyntax, firstTyped⟩ := firstIH firstReached
    obtain ⟨secondSyntax, secondTyped⟩ := secondIH secondReached
    refine ⟨.pair ((expression_lookup edited avoids reached).symm.trans found) form firstSyntax secondSyntax, step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact firstTyped
      · exact secondTyped
  | @unary id node operand operator found form child ih =>
    have childReached : Reaches source roots (.expression operand) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    obtain ⟨certified, typed⟩ := ih childReached
    refine ⟨.unary ((expression_lookup edited avoids reached).symm.trans found) form certified, step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren, List.mem_singleton] at member
      subst child
      exact typed
  | @binary id node left right operator found form first second firstIH secondIH =>
    have firstReached : Reaches source roots (.expression left) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    have secondReached : Reaches source roots (.expression right) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    obtain ⟨firstSyntax, firstTyped⟩ := firstIH firstReached
    obtain ⟨secondSyntax, secondTyped⟩ := secondIH secondReached
    refine ⟨.binary ((expression_lookup edited avoids reached).symm.trans found) form firstSyntax secondSyntax, step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact firstTyped
      · exact secondTyped
  | @conditional id node condition thenId elseId found form conditionSyntax first second conditionIH firstIH secondIH =>
    have conditionReached : Reaches source roots (.expression condition) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    have firstReached : Reaches source roots (.expression thenId) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    have secondReached : Reaches source roots (.expression elseId) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    obtain ⟨conditionSyntax, conditionTyped⟩ := conditionIH conditionReached
    obtain ⟨firstSyntax, firstTyped⟩ := firstIH firstReached
    obtain ⟨secondSyntax, secondTyped⟩ := secondIH secondReached
    refine ⟨.conditional ((expression_lookup edited avoids reached).symm.trans found) form conditionSyntax firstSyntax secondSyntax, step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · exact conditionTyped
      · exact firstTyped
      · exact secondTyped

include edited avoids unique in
private theorem constructors {id : ExpressionId} (syntaxTree : CompatibleExpressionConstructors.Syntax source id)
    (reached : Reaches source roots (.expression id)) :
    CompatibleExpressionConstructors.Syntax view id ∧ TypedAt source view id := by
  induction syntaxTree with
  | fragment child =>
    obtain ⟨certified, typed⟩ := conditionals edited avoids unique child reached
    exact ⟨.fragment certified, typed⟩
  | @constructor id node instantiation ids found form children ih =>
    have transported := fun child member => ih child member
      (Reaches.expression reached found (by simp [form, ExpressionForm.references, member]))
    refine ⟨.constructor ((expression_lookup edited avoids reached).symm.trans found) form (fun child member => (transported child member).1),
      step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren] at member
      exact (transported child member).2

include edited avoids unique in
private theorem members {id : ExpressionId} (syntaxTree : CompatibleExpressionMembers.Syntax source id)
    (reached : Reaches source roots (.expression id)) :
    CompatibleExpressionMembers.Syntax view id ∧ TypedAt source view id := by
  induction syntaxTree with
  | fragment child =>
    obtain ⟨certified, typed⟩ := constructors edited avoids unique child reached
    exact ⟨.fragment certified, typed⟩
  | @member id node base name index found form child ih =>
    have childReached : Reaches source roots (.expression base) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    obtain ⟨certified, typed⟩ := ih childReached
    refine ⟨.member ((expression_lookup edited avoids reached).symm.trans found) form certified, step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren, List.mem_singleton] at member
      subst child
      exact typed

include edited avoids unique in
private theorem recursive {id : ExpressionId} (syntaxTree : CompatibleExpressionRecursive.Syntax source id)
    (reached : Reaches source roots (.expression id)) :
    CompatibleExpressionRecursive.Syntax view id ∧ TypedAt source view id := by
  induction syntaxTree with
  | fragment child =>
    obtain ⟨certified, typed⟩ := members edited avoids unique child reached
    exact ⟨.fragment certified, typed⟩
  | @group id node inner found form child ih =>
    have childReached : Reaches source roots (.expression inner) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    obtain ⟨certified, typed⟩ := ih childReached
    refine ⟨.group ((expression_lookup edited avoids reached).symm.trans found) form certified, step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren, List.mem_singleton] at member
      subst child
      exact typed
  | @pair id node left right found form first second firstIH secondIH =>
    have firstReached : Reaches source roots (.expression left) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    have secondReached : Reaches source roots (.expression right) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    obtain ⟨firstSyntax, firstTyped⟩ := firstIH firstReached
    obtain ⟨secondSyntax, secondTyped⟩ := secondIH secondReached
    refine ⟨.pair ((expression_lookup edited avoids reached).symm.trans found) form firstSyntax secondSyntax, step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact firstTyped
      · exact secondTyped
  | @unary id node operand operator found form child ih =>
    have childReached : Reaches source roots (.expression operand) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    obtain ⟨certified, typed⟩ := ih childReached
    refine ⟨.unary ((expression_lookup edited avoids reached).symm.trans found) form certified, step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren, List.mem_singleton] at member
      subst child
      exact typed
  | @binary id node left right operator found form first second firstIH secondIH =>
    have firstReached : Reaches source roots (.expression left) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    have secondReached : Reaches source roots (.expression right) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    obtain ⟨firstSyntax, firstTyped⟩ := firstIH firstReached
    obtain ⟨secondSyntax, secondTyped⟩ := secondIH secondReached
    refine ⟨.binary ((expression_lookup edited avoids reached).symm.trans found) form firstSyntax secondSyntax, step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact firstTyped
      · exact secondTyped
  | @conditional id node condition thenId elseId found form conditionSyntax first second conditionIH firstIH secondIH =>
    have conditionReached : Reaches source roots (.expression condition) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    have firstReached : Reaches source roots (.expression thenId) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    have secondReached : Reaches source roots (.expression elseId) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    obtain ⟨conditionSyntax, conditionTyped⟩ := conditionIH conditionReached
    obtain ⟨firstSyntax, firstTyped⟩ := firstIH firstReached
    obtain ⟨secondSyntax, secondTyped⟩ := secondIH secondReached
    refine ⟨.conditional ((expression_lookup edited avoids reached).symm.trans found) form conditionSyntax firstSyntax secondSyntax, step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · exact conditionTyped
      · exact firstTyped
      · exact secondTyped
  | @constructor id node instantiation ids found form children ih =>
    have transported := fun child member => ih child member
      (Reaches.expression reached found (by simp [form, ExpressionForm.references, member]))
    refine ⟨.constructor ((expression_lookup edited avoids reached).symm.trans found) form (fun child member => (transported child member).1),
      step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren] at member
      exact (transported child member).2
  | @member id node base name index found form child ih =>
    have childReached : Reaches source roots (.expression base) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    obtain ⟨certified, typed⟩ := ih childReached
    refine ⟨.member ((expression_lookup edited avoids reached).symm.trans found) form certified, step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren, List.mem_singleton] at member
      subst child
      exact typed

include edited avoids unique in
private theorem general {id : ExpressionId} (syntaxTree : CompatibleExpressionGeneral.Syntax source id)
    (reached : Reaches source roots (.expression id)) :
    CompatibleExpressionGeneral.Syntax view id ∧ TypedAt source view id := by
  induction syntaxTree with
  | fragment child =>
    obtain ⟨certified, typed⟩ := recursive edited avoids unique child reached
    exact ⟨.fragment certified, typed⟩
  | proxy found form =>
    refine ⟨.proxy ((expression_lookup edited avoids reached).symm.trans found) form, step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · simp [form, typingChildren]
  | @group id node inner found form child ih =>
    have childReached : Reaches source roots (.expression inner) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    obtain ⟨certified, typed⟩ := ih childReached
    refine ⟨.group ((expression_lookup edited avoids reached).symm.trans found) form certified, step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren, List.mem_singleton] at member
      subst child
      exact typed
  | @pair id node left right found form first second firstIH secondIH =>
    have firstReached : Reaches source roots (.expression left) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    have secondReached : Reaches source roots (.expression right) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    obtain ⟨firstSyntax, firstTyped⟩ := firstIH firstReached
    obtain ⟨secondSyntax, secondTyped⟩ := secondIH secondReached
    refine ⟨.pair ((expression_lookup edited avoids reached).symm.trans found) form firstSyntax secondSyntax, step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact firstTyped
      · exact secondTyped
  | @unary id node operand operator found form child ih =>
    have childReached : Reaches source roots (.expression operand) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    obtain ⟨certified, typed⟩ := ih childReached
    refine ⟨.unary ((expression_lookup edited avoids reached).symm.trans found) form certified, step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren, List.mem_singleton] at member
      subst child
      exact typed
  | @binary id node left right operator found form first second firstIH secondIH =>
    have firstReached : Reaches source roots (.expression left) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    have secondReached : Reaches source roots (.expression right) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    obtain ⟨firstSyntax, firstTyped⟩ := firstIH firstReached
    obtain ⟨secondSyntax, secondTyped⟩ := secondIH secondReached
    refine ⟨.binary ((expression_lookup edited avoids reached).symm.trans found) form firstSyntax secondSyntax, step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact firstTyped
      · exact secondTyped
  | @conditional id node condition thenId elseId found form conditionSyntax first second conditionIH firstIH secondIH =>
    have conditionReached : Reaches source roots (.expression condition) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    have firstReached : Reaches source roots (.expression thenId) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    have secondReached : Reaches source roots (.expression elseId) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    obtain ⟨conditionSyntax, conditionTyped⟩ := conditionIH conditionReached
    obtain ⟨firstSyntax, firstTyped⟩ := firstIH firstReached
    obtain ⟨secondSyntax, secondTyped⟩ := secondIH secondReached
    refine ⟨.conditional ((expression_lookup edited avoids reached).symm.trans found) form conditionSyntax firstSyntax secondSyntax, step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · exact conditionTyped
      · exact firstTyped
      · exact secondTyped
  | @constructor id node instantiation ids found form children ih =>
    have transported := fun child member => ih child member
      (Reaches.expression reached found (by simp [form, ExpressionForm.references, member]))
    refine ⟨.constructor ((expression_lookup edited avoids reached).symm.trans found) form (fun child member => (transported child member).1),
      step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren] at member
      exact (transported child member).2
  | @member id node base name index found form child ih =>
    have childReached : Reaches source roots (.expression base) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    obtain ⟨certified, typed⟩ := ih childReached
    refine ⟨.member ((expression_lookup edited avoids reached).symm.trans found) form certified, step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren, List.mem_singleton] at member
      subst child
      exact typed
  | @index id node base key keyNode found form keyFound first second firstIH secondIH =>
    have firstReached : Reaches source roots (.expression base) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    have secondReached : Reaches source roots (.expression key) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    obtain ⟨firstSyntax, firstTyped⟩ := firstIH firstReached
    obtain ⟨secondSyntax, secondTyped⟩ := secondIH secondReached
    refine ⟨.index ((expression_lookup edited avoids reached).symm.trans found) form ((expression_lookup edited avoids secondReached).symm.trans keyFound) firstSyntax secondSyntax, step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact firstTyped
      · exact secondTyped

include edited avoids unique in
private theorem builtins {id : ExpressionId} (syntaxTree : CompatibleExpressionBuiltins.Syntax source id)
    (reached : Reaches source roots (.expression id)) :
    CompatibleExpressionBuiltins.Syntax view id ∧ TypedAt source view id := by
  induction syntaxTree with
  | fragment child =>
    obtain ⟨certified, typed⟩ := general edited avoids unique child reached
    exact ⟨.fragment certified, typed⟩
  | proxy found form =>
    refine ⟨.proxy ((expression_lookup edited avoids reached).symm.trans found) form, step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · simp [form, typingChildren]
  | @group id node inner found form child ih =>
    have childReached : Reaches source roots (.expression inner) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    obtain ⟨certified, typed⟩ := ih childReached
    refine ⟨.group ((expression_lookup edited avoids reached).symm.trans found) form certified, step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren, List.mem_singleton] at member
      subst child
      exact typed
  | @pair id node left right found form first second firstIH secondIH =>
    have firstReached : Reaches source roots (.expression left) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    have secondReached : Reaches source roots (.expression right) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    obtain ⟨firstSyntax, firstTyped⟩ := firstIH firstReached
    obtain ⟨secondSyntax, secondTyped⟩ := secondIH secondReached
    refine ⟨.pair ((expression_lookup edited avoids reached).symm.trans found) form firstSyntax secondSyntax, step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact firstTyped
      · exact secondTyped
  | @unary id node operand operator found form child ih =>
    have childReached : Reaches source roots (.expression operand) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    obtain ⟨certified, typed⟩ := ih childReached
    refine ⟨.unary ((expression_lookup edited avoids reached).symm.trans found) form certified, step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren, List.mem_singleton] at member
      subst child
      exact typed
  | @binary id node left right operator found form first second firstIH secondIH =>
    have firstReached : Reaches source roots (.expression left) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    have secondReached : Reaches source roots (.expression right) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    obtain ⟨firstSyntax, firstTyped⟩ := firstIH firstReached
    obtain ⟨secondSyntax, secondTyped⟩ := secondIH secondReached
    refine ⟨.binary ((expression_lookup edited avoids reached).symm.trans found) form firstSyntax secondSyntax, step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact firstTyped
      · exact secondTyped
  | @conditional id node condition thenId elseId found form conditionSyntax first second conditionIH firstIH secondIH =>
    have conditionReached : Reaches source roots (.expression condition) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    have firstReached : Reaches source roots (.expression thenId) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    have secondReached : Reaches source roots (.expression elseId) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    obtain ⟨conditionSyntax, conditionTyped⟩ := conditionIH conditionReached
    obtain ⟨firstSyntax, firstTyped⟩ := firstIH firstReached
    obtain ⟨secondSyntax, secondTyped⟩ := secondIH secondReached
    refine ⟨.conditional ((expression_lookup edited avoids reached).symm.trans found) form conditionSyntax firstSyntax secondSyntax, step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · exact conditionTyped
      · exact firstTyped
      · exact secondTyped
  | @constructor id node instantiation ids found form children ih =>
    have transported := fun child member => ih child member
      (Reaches.expression reached found (by simp [form, ExpressionForm.references, member]))
    refine ⟨.constructor ((expression_lookup edited avoids reached).symm.trans found) form (fun child member => (transported child member).1),
      step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren] at member
      exact (transported child member).2
  | @member id node base name index found form child ih =>
    have childReached : Reaches source roots (.expression base) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    obtain ⟨certified, typed⟩ := ih childReached
    refine ⟨.member ((expression_lookup edited avoids reached).symm.trans found) form certified, step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren, List.mem_singleton] at member
      subst child
      exact typed
  | @index id node base key keyNode found form keyFound first second firstIH secondIH =>
    have firstReached : Reaches source roots (.expression base) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    have secondReached : Reaches source roots (.expression key) := Reaches.expression reached found (by simp [form, ExpressionForm.references])
    obtain ⟨firstSyntax, firstTyped⟩ := firstIH firstReached
    obtain ⟨secondSyntax, secondTyped⟩ := secondIH secondReached
    refine ⟨.index ((expression_lookup edited avoids reached).symm.trans found) form ((expression_lookup edited avoids secondReached).symm.trans keyFound) firstSyntax secondSyntax, step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact firstTyped
      · exact secondTyped
  | @builtin id node callee arguments function found form children ih =>
    have transported := fun child member => ih child member
      (Reaches.expression reached found (by simp [form, ExpressionForm.references, member]))
    refine ⟨.builtin ((expression_lookup edited avoids reached).symm.trans found) form (fun child member => (transported child member).1),
      step edited avoids unique reached found ?_ ?_⟩
    · simp [form, BodyFree]
    · intro child member
      simp only [form, typingChildren] at member
      exact (transported child member).2

include edited avoids unique in
/-- The complete ordinary builtin syntax is transported only on reached nodes. -/
theorem expression_syntax {id : ExpressionId}
    (syntaxTree : CompatibleExpressionBuiltins.Syntax source id)
    (reached : Reaches source roots (.expression id)) :
    CompatibleExpressionBuiltins.Syntax view id :=
  (builtins edited avoids unique syntaxTree reached).1

include edited avoids unique in
/-- Full independent typing retains the actual raw type, requirements and
coercions, including the reached builtin callee's declaration metadata. -/
theorem expression_typing {id : ExpressionId} {context : Context} {type : TypeSystem.Ty}
    (syntaxTree : CompatibleExpressionBuiltins.Syntax source id)
    (reached : Reaches source roots (.expression id))
    (typed : ExpressionHasType source context id type) :
    ExpressionHasType view context id type :=
  (builtins edited avoids unique syntaxTree reached).2 context type typed

include edited in
private theorem reversed : LocalView view source changed :=
  ⟨edited.metadata.symm, fun id fresh => (edited.unchanged id fresh).symm⟩

include edited avoids unique in
/-- An accepted view's independent syntax recovers canonical source syntax.
Freshness and uniqueness are stated on the canonical source. -/
theorem expression_syntax_original {id : ExpressionId}
    (syntaxTree : CompatibleExpressionBuiltins.Syntax view id)
    (reached : Reaches source roots (.expression id)) :
    CompatibleExpressionBuiltins.Syntax source id :=
  expression_syntax (reversed edited) (avoids.view edited.metadata) (edited.metadata.unique unique)
    syntaxTree (reached.metadata edited.metadata)

include edited avoids unique in
/-- The actual view's independent expression typing also recovers canonical
source typing; canonical compiler acceptance is not an assumption. -/
theorem expression_typing_original {id : ExpressionId} {context : Context} {type : TypeSystem.Ty}
    (syntaxTree : CompatibleExpressionBuiltins.Syntax view id)
    (reached : Reaches source roots (.expression id))
    (typed : ExpressionHasType view context id type) :
    ExpressionHasType source context id type :=
  expression_typing (reversed edited) (avoids.view edited.metadata) (edited.metadata.unique unique)
    syntaxTree (reached.metadata edited.metadata) typed

include edited avoids unique in
/-- Ordinary let/block/if syntax, with its independent expression typing,
transports at the actual lexical contexts. No body execution is stored here. -/
theorem lexical_syntax {context : Context} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty}
    (syntaxTree : BuiltinLexicalStatements.Syntax source context mode statements expected)
    (reached : ∀ id ∈ statements, Reaches source roots (.statement id)) :
    BuiltinLexicalStatements.Syntax view context mode statements expected := by
  induction syntaxTree with
  | nil allowed => exact .nil allowed
  | returnUnit rest found form sourceType =>
    exact .returnUnit rest (edited.metadata.symm.statement found) form sourceType
  | @returnValue context mode id node expression expressionNode expected rest found form sourceType expressionFound valueType typed value =>
    have child : Reaches source roots (.expression expression) :=
      .statement (reached id (by simp)) found (by simp [form, StatementForm.references])
    obtain ⟨certified, typing⟩ := builtins edited avoids unique value child
    exact .returnValue rest (edited.metadata.symm.statement found) form sourceType
      ((expression_lookup edited avoids child).symm.trans expressionFound) valueType (typing _ _ typed) certified
  | @tail context id node expression expressionNode expected found form sourceType expressionFound valueType typed value =>
    have child : Reaches source roots (.expression expression) :=
      .statement (reached id (by simp)) found (by simp [form, StatementForm.references])
    obtain ⟨certified, typing⟩ := builtins edited avoids unique value child
    exact .tail (edited.metadata.symm.statement found) form sourceType
      ((expression_lookup edited avoids child).symm.trans expressionFound) valueType (typing _ _ typed) certified
  | @uninitialized context nextContext mode id node binder rest expected found form declaration mono extended ordinary remaining ih =>
    exact .uninitialized (edited.metadata.symm.statement found) form
      ((rootBinder edited.metadata binder.id).symm.trans declaration) mono
      (by simpa only [edited.metadata.owner] using extended)
      (by simpa only [edited.metadata.inputs] using ordinary)
      (ih (fun child member => reached child (List.mem_cons_of_mem id member)))
  | @initialized context nextContext mode id node binder initializer initializerNode rest expected found form declaration mono extended ordinary initializerFound sourceType initializerTyped initializerSyntax remaining ih =>
    have child : Reaches source roots (.expression initializer) :=
      .statement (reached id (by simp)) found (by simp [form, StatementForm.references])
    obtain ⟨certified, typing⟩ := builtins edited avoids unique initializerSyntax child
    exact .initialized (edited.metadata.symm.statement found) form
      ((rootBinder edited.metadata binder.id).symm.trans declaration) mono
      (by simpa only [edited.metadata.owner] using extended)
      (by simpa only [edited.metadata.inputs] using ordinary)
      ((expression_lookup edited avoids child).symm.trans initializerFound) sourceType
      (typing _ _ initializerTyped) certified
      (ih (fun child member => reached child (List.mem_cons_of_mem id member)))
  | @discard context mode id node expression expressionNode semicolon rest expected found form notTail sourceType expressionFound typed value remaining ih =>
    have child : Reaches source roots (.expression expression) :=
      .statement (reached id (by simp)) found (by simp [form, StatementForm.references])
    obtain ⟨certified, typing⟩ := builtins edited avoids unique value child
    exact .discard (edited.metadata.symm.statement found) form notTail sourceType
      ((expression_lookup edited avoids child).symm.trans expressionFound) (typing _ _ typed) certified
      (ih (fun child member => reached child (List.mem_cons_of_mem id member)))
  | @block context mode id node statements rest expected found form sourceType inner remaining innerIH restIH =>
    exact .block (edited.metadata.symm.statement found) form sourceType
      (innerIH (fun child member => .statement (reached id (by simp)) found
        (by simp [form, StatementForm.references, member])))
      (restIH (fun child member => reached child (List.mem_cons_of_mem id member)))
  | @ifThen context mode id node condition conditionNode thenBody elseBody rest expected found form sourceType conditionFound conditionType typed conditionSyntax thenSyntax elseSyntax remaining thenIH elseIH restIH =>
    have child : Reaches source roots (.expression condition) :=
      .statement (reached id (by simp)) found (by simp [form, StatementForm.references])
    obtain ⟨certified, typing⟩ := builtins edited avoids unique conditionSyntax child
    exact .ifThen (edited.metadata.symm.statement found) form sourceType
      ((expression_lookup edited avoids child).symm.trans conditionFound) conditionType (typing _ _ typed) certified
      (thenIH (fun child member => .statement (reached id (by simp)) found
        (by simp [form, StatementForm.references, member])))
      (elseIH (fun child member => .statement (reached id (by simp)) found
        (by simp [form, StatementForm.references, member])))
      (restIH (fun child member => reached child (List.mem_cons_of_mem id member)))

include edited avoids unique in
theorem lexical_syntax_original {context : Context} {mode : Bool} {statements : List StatementId}
    {expected : TypeSystem.Ty}
    (syntaxTree : BuiltinLexicalStatements.Syntax view context mode statements expected)
    (reached : ∀ id ∈ statements, Reaches source roots (.statement id)) :
    BuiltinLexicalStatements.Syntax source context mode statements expected :=
  lexical_syntax (reversed edited) (avoids.view edited.metadata) (edited.metadata.unique unique)
    syntaxTree (fun id member => (reached id member).metadata edited.metadata)

/-- Every statement in the actual body is its own reachability root. -/
theorem body_syntax {source view : TypedSource} {changed : List ExpressionId}
    {context : Context} {mode : Bool} {statements : List StatementId} {expected : TypeSystem.Ty}
    (edited : LocalView source view changed)
    (avoids : Avoids source (statements.map NodeId.statement) changed)
    (unique : NodeOccurrencesUnique source)
    (syntaxTree : BuiltinLexicalStatements.Syntax source context mode statements expected) :
    BuiltinLexicalStatements.Syntax view context mode statements expected :=
  lexical_syntax edited avoids unique syntaxTree (fun id member => .root (List.mem_map.mpr ⟨id, member, rfl⟩))

/-- Canonical lexical syntax is recovered from view syntax without assuming
whole StatementsHaveType transport or canonical compiler success. -/
theorem body_syntax_original {source view : TypedSource} {changed : List ExpressionId}
    {context : Context} {mode : Bool} {statements : List StatementId} {expected : TypeSystem.Ty}
    (edited : LocalView source view changed)
    (avoids : Avoids source (statements.map NodeId.statement) changed)
    (unique : NodeOccurrencesUnique source)
    (syntaxTree : BuiltinLexicalStatements.Syntax view context mode statements expected) :
    BuiltinLexicalStatements.Syntax source context mode statements expected :=
  lexical_syntax_original edited avoids unique syntaxTree (fun id member => .root (List.mem_map.mpr ⟨id, member, rfl⟩))

end Solcore.SourceSemantics.CoreLowering.CallableLambdaViewSourceTyping
