import Solcore.Surface.Multi.Diagnostic

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Solcore.Workspace

namespace NonemptyList

/-- View the local nonempty-list carrier in its written order. -/
def toList {α : Type} (values : NonemptyList α) : List α :=
  values.head :: values.tail

@[simp] theorem toList_mk {α : Type} (head : α) (tail : List α) :
    (NonemptyList.mk head tail).toList = head :: tail :=
  rfl

@[simp] theorem mem_toList {α : Type} {value : α}
    {values : NonemptyList α} :
    value ∈ values.toList ↔ value = values.head ∨ value ∈ values.tail := by
  simp [toList]

end NonemptyList

namespace FiniteList

/-- Structural membership decision using the supplied propositional equality. -/
def memDecidable {α : Type} [DecidableEq α] (value : α) :
    (values : List α) → Decidable (value ∈ values)
  | [] => isFalse (by simp)
  | head :: tail =>
      if equal : value = head then
        isTrue (by simp [equal])
      else
        match memDecidable value tail with
        | isTrue member => isTrue (by simp [member])
        | isFalse absent => isFalse (by simp [equal, absent])

/-- Decide a bounded existential by traversing its finite list. -/
def existsMemDecidable {α : Type} (predicate : α → Prop)
    (decidePredicate : (value : α) → Decidable (predicate value)) :
    (values : List α) → Decidable (∃ value ∈ values, predicate value)
  | [] => isFalse (by simp)
  | head :: tail =>
      match decidePredicate head with
      | isTrue accepted => isTrue ⟨head, by simp, accepted⟩
      | isFalse rejected =>
          match existsMemDecidable predicate decidePredicate tail with
          | isTrue accepted =>
              isTrue ⟨accepted.choose,
                List.mem_cons_of_mem head accepted.choose_spec.1,
                accepted.choose_spec.2⟩
          | isFalse rejectedTail => isFalse (by
              rintro ⟨value, member, accepted⟩
              rcases List.mem_cons.mp member with equal | memberTail
              · subst value
                exact rejected accepted
              · exact rejectedTail ⟨value, memberTail, accepted⟩)

/-- Decide a bounded universal by traversing its finite list. -/
def forallMemDecidable {α : Type} (predicate : α → Prop)
    (decidePredicate : (value : α) → Decidable (predicate value)) :
    (values : List α) → Decidable (∀ value ∈ values, predicate value)
  | [] => isTrue (by simp)
  | head :: tail =>
      match decidePredicate head with
      | isFalse rejected => isFalse (by
          intro accepted
          exact rejected (accepted head (by simp)))
      | isTrue accepted =>
          match forallMemDecidable predicate decidePredicate tail with
          | isTrue acceptedTail => isTrue (by
              intro value member
              rcases List.mem_cons.mp member with equal | memberTail
              · subst value
                exact accepted
              · exact acceptedTail value memberTail)
          | isFalse rejectedTail => isFalse (by
              intro acceptedAll
              exact rejectedTail fun value member =>
                acceptedAll value (List.mem_cons_of_mem head member))

end FiniteList

/--
One occurrence equal to `later` has an equal key at a strictly earlier list
position.  The recursive definition keeps occurrence order explicit without
using the structural validator's duplicate collector.
-/
def LaterDuplicate {α κ : Type}
    (values : List α) (key : α → κ) (later : α) : Prop :=
  match values with
  | [] => False
  | head :: tail =>
      LaterDuplicate tail key later ∨
        ∃ candidate ∈ tail,
          candidate = later ∧ key head = key candidate

@[simp] theorem laterDuplicate_nil {α κ : Type}
    (key : α → κ) (later : α) :
    ¬LaterDuplicate [] key later := by
  simp [LaterDuplicate]

@[simp] theorem laterDuplicate_cons_iff {α κ : Type}
    (head : α) (tail : List α) (key : α → κ) (later : α) :
    LaterDuplicate (head :: tail) key later ↔
      LaterDuplicate tail key later ∨
        ∃ candidate ∈ tail,
          candidate = later ∧ key head = key candidate := by
  rfl

/-- A duplicate already present in a suffix remains later in a larger list. -/
theorem LaterDuplicate.of_tail {α κ : Type}
    {head later : α} {tail : List α} {key : α → κ}
    (duplicate : LaterDuplicate tail key later) :
    LaterDuplicate (head :: tail) key later :=
  Or.inl duplicate

/-- The head supplies an earlier equal key for a selected later occurrence. -/
theorem LaterDuplicate.of_head {α κ : Type}
    {head candidate later : α} {tail : List α} {key : α → κ}
    (member : candidate ∈ tail)
    (candidateEq : candidate = later)
    (keyEq : key head = key candidate) :
    LaterDuplicate (head :: tail) key later :=
  Or.inr ⟨candidate, member, candidateEq, keyEq⟩

/-- `LaterDuplicate` is decidable for decidable values and keys. -/
def LaterDuplicate.decidable {α κ : Type}
    [DecidableEq α] [DecidableEq κ]
    (key : α → κ) (later : α) :
    (values : List α) → Decidable (LaterDuplicate values key later)
  | [] => isFalse (by simp [LaterDuplicate])
  | head :: tail =>
      letI : Decidable (LaterDuplicate tail key later) :=
        LaterDuplicate.decidable key later tail
      if suffix : LaterDuplicate tail key later then
        isTrue (Or.inl suffix)
      else
        let predicate := fun candidate : α =>
          candidate = later ∧ key head = key candidate
        let decidePredicate : (candidate : α) → Decidable (predicate candidate) :=
          fun _ => inferInstance
        match FiniteList.existsMemDecidable
            predicate decidePredicate tail with
        | isTrue matched => isTrue (Or.inr matched)
        | isFalse notMatched =>
            isFalse (by
              rw [laterDuplicate_cons_iff]
              exact fun alternatives => alternatives.elim suffix notMatched)

instance {α κ : Type} [DecidableEq α] [DecidableEq κ]
    (values : List α) (key : α → κ) (later : α) :
    Decidable (LaterDuplicate values key later) :=
  LaterDuplicate.decidable key later values

/-- Strict source, start-byte, and end-byte order for primary spans. -/
def SpanBefore (left right : SourceSpan) : Prop :=
  SourceId.compare left.source right.source = .lt ∨
    (left.source = right.source ∧
      (left.startByte < right.startByte ∨
        (left.startByte = right.startByte ∧
          left.endByte < right.endByte)))

instance (left right : SourceSpan) : Decidable (SpanBefore left right) := by
  unfold SpanBefore
  infer_instance

@[simp] theorem spanBefore_self (span : SourceSpan) :
    ¬SpanBefore span span := by
  have reflexive : SourceId.compare span.source span.source = .eq :=
    Std.ReflCmp.compare_self
  simp [SpanBefore, reflexive]

/-- A strictly earlier source identity makes the whole span earlier. -/
theorem SpanBefore.of_source
    {left right : SourceSpan}
    (sourceBefore : SourceId.compare left.source right.source = .lt) :
    SpanBefore left right :=
  Or.inl sourceBefore

/-- At one source, a strictly earlier start byte makes the span earlier. -/
theorem SpanBefore.of_start
    {left right : SourceSpan}
    (sourceEq : left.source = right.source)
    (startBefore : left.startByte < right.startByte) :
    SpanBefore left right :=
  Or.inr ⟨sourceEq, Or.inl startBefore⟩

/-- Equal source and start coordinates defer the order to the end byte. -/
theorem SpanBefore.of_end
    {left right : SourceSpan}
    (sourceEq : left.source = right.source)
    (startEq : left.startByte = right.startByte)
    (endBefore : left.endByte < right.endByte) :
    SpanBefore left right :=
  Or.inr ⟨sourceEq, Or.inr ⟨startEq, endBefore⟩⟩

/-- No span in a finite list is strictly before the selected span. -/
def NoSpanBefore (span : SourceSpan) : List SourceSpan → Prop
  | [] => True
  | candidate :: rest =>
      ¬SpanBefore candidate span ∧ NoSpanBefore span rest

/-- The recursive finite condition is the corresponding bounded universal. -/
@[simp] theorem noSpanBefore_iff
    (span : SourceSpan) (spans : List SourceSpan) :
    NoSpanBefore span spans ↔
      ∀ candidate ∈ spans, ¬SpanBefore candidate span := by
  induction spans with
  | nil => simp [NoSpanBefore]
  | cons head tail induction =>
      simp [NoSpanBefore, induction]

/-- The finite absence condition has a structural decision procedure. -/
def NoSpanBefore.decidable (span : SourceSpan) :
    (spans : List SourceSpan) → Decidable (NoSpanBefore span spans)
  | [] => isTrue True.intro
  | candidate :: rest => by
      letI : Decidable (NoSpanBefore span rest) :=
        NoSpanBefore.decidable span rest
      change Decidable
        (¬SpanBefore candidate span ∧ NoSpanBefore span rest)
      infer_instance

instance (span : SourceSpan) (spans : List SourceSpan) :
    Decidable (NoSpanBefore span spans) :=
  NoSpanBefore.decidable span spans

/-- A listed span is least when no listed candidate is strictly before it. -/
def LeastSpanIn (span : SourceSpan) (spans : List SourceSpan) : Prop :=
  span ∈ spans ∧ NoSpanBefore span spans

instance (span : SourceSpan) (spans : List SourceSpan) :
    Decidable (LeastSpanIn span spans) := by
  match FiniteList.memDecidable span spans with
  | isFalse notMember =>
      exact isFalse fun least => notMember least.1
  | isTrue member =>
      match NoSpanBefore.decidable span spans with
      | isTrue noEarlier => exact isTrue ⟨member, noEarlier⟩
      | isFalse notNoEarlier =>
          exact isFalse fun least => notNoEarlier least.2

@[simp] theorem leastSpanIn_nil (span : SourceSpan) :
    ¬LeastSpanIn span [] := by
  simp [LeastSpanIn]

@[simp] theorem leastSpanIn_singleton (span : SourceSpan) :
    LeastSpanIn span [span] := by
  simp [LeastSpanIn]

/-- A least span is one of the candidate spans. -/
theorem LeastSpanIn.member {span : SourceSpan} {spans : List SourceSpan}
    (least : LeastSpanIn span spans) :
    span ∈ spans :=
  least.1

/-- Nothing in the same candidate list is strictly before its least span. -/
theorem LeastSpanIn.not_before
    {span candidate : SourceSpan} {spans : List SourceSpan}
    (least : LeastSpanIn span spans)
    (member : candidate ∈ spans) :
    ¬SpanBefore candidate span :=
  (noSpanBefore_iff span spans).mp least.2 candidate member

/-- A fallback return type after removing only explicit groups is unit. -/
inductive GroupedUnit : TypeExpr → Prop where
  | unitTuple (span : SourceSpan) :
      GroupedUnit ⟨span, .tuple []⟩
  | group (span : SourceSpan) (inner : TypeExpr) :
      GroupedUnit inner → GroupedUnit ⟨span, .group inner⟩

@[simp] theorem groupedUnit_tuple_iff
    (span : SourceSpan) (elements : List TypeExpr) :
    GroupedUnit (show TypeExpr from ⟨span, .tuple elements⟩) ↔
      elements = [] := by
  constructor
  · intro accepted
    cases accepted
    rfl
  · intro empty
    subst elements
    exact .unitTuple span

@[simp] theorem groupedUnit_group_iff
    (span : SourceSpan) (inner : TypeExpr) :
    GroupedUnit (show TypeExpr from ⟨span, .group inner⟩) ↔
      GroupedUnit inner := by
  constructor
  · intro accepted
    cases accepted
    assumption
  · exact .group span inner

/-- Executable decision for the independent grouped-unit relation. -/
def groupedUnitBool : TypeExpr → Bool
  | ⟨_, .tuple []⟩ => true
  | ⟨_, .group inner⟩ => groupedUnitBool inner
  | _ => false
termination_by expression => sizeOf expression

@[simp] theorem groupedUnitBool_eq_true_iff :
    ∀ expression : TypeExpr,
      groupedUnitBool expression = true ↔ GroupedUnit expression := by
  intro expression
  rcases expression with ⟨span, payload⟩
  cases payload with
  | tuple elements =>
      cases elements with
      | nil =>
          simp only [groupedUnitBool]
          exact ⟨fun _ => .unitTuple span, fun _ => True.intro⟩
      | cons head tail =>
          simp only [groupedUnitBool, Bool.false_eq_true]
          exact ⟨False.elim, fun accepted => by cases accepted⟩
  | group inner =>
      simp only [groupedUnitBool]
      rw [groupedUnitBool_eq_true_iff inner]
      exact ⟨fun accepted => .group span inner accepted,
        fun accepted => by cases accepted; assumption⟩
  | named name arguments =>
      simp only [groupedUnitBool, Bool.false_eq_true]
      exact ⟨False.elim, fun accepted => by cases accepted⟩
  | proxy marker inner =>
      simp only [groupedUnitBool, Bool.false_eq_true]
      exact ⟨False.elim, fun accepted => by cases accepted⟩
  | «function» domain codomain =>
      simp only [groupedUnitBool, Bool.false_eq_true]
      exact ⟨False.elim, fun accepted => by cases accepted⟩
  | comptime marker inner =>
      simp only [groupedUnitBool, Bool.false_eq_true]
      exact ⟨False.elim, fun accepted => by cases accepted⟩
termination_by expression => sizeOf expression

instance (expression : TypeExpr) : Decidable (GroupedUnit expression) :=
  decidable_of_iff
    (groupedUnitBool expression = true)
    (groupedUnitBool_eq_true_iff expression)

/-- The typed sites traversed by the independent structural judgment. -/
inductive StructuralSite where
  | importSelection (selection : ImportSelection)
  | hidingClause (clause : HidingClause)
  | localExportList (selection : LocalExportList)
  | remoteExportSelection (selection : RemoteExportSelection)
  | exportItem (item : ExportItem)
  | pragma (declaration : PragmaDecl)
  | signature
      (modifierContext : Option ModifierContext)
      (parameterContext : ParameterContext)
      (signature : FunctionSignature)
  | fallback (declaration : FallbackDecl)
  | contractConstructor (declaration : ContractConstructorDecl)
  | expression (expression : Expression)
  | pattern (pattern : Pattern)
  | body (loopDepth : Nat) (body : Body)
  | statement (loopDepth : Nat) (statement : Statement)
  | forInit (item : ForInitItem)
  | forPost (item : ForPostItem)

namespace StructuralSite

/--
Independent reachability of every site inspected by structural validation.
Declaration roots come directly from the module.  Recursive constructors
follow only semantic AST children; statement bodies retain their loop depth,
`for` bodies increase it, and lambda bodies restart it at zero.
-/
inductive Occurs (module : ParsedModuleV1) : StructuralSite → Prop where
  | importSelectionTop
      {item : TopItem} {declaration : ImportDecl}
      {selection : ImportSelection}
      {hidingClause : Option HidingClause}
      (itemMember : item ∈ module.payload.items)
      (itemShape : item.payload = .importDecl declaration)
      (modeShape : declaration.payload.mode =
        .items selection hidingClause) :
      Occurs module (.importSelection selection)
  | hidingClauseTop
      {item : TopItem} {declaration : ImportDecl}
      {selection : ImportSelection} {clause : HidingClause}
      (itemMember : item ∈ module.payload.items)
      (itemShape : item.payload = .importDecl declaration)
      (modeShape : declaration.payload.mode =
        .items selection (some clause)) :
      Occurs module (.hidingClause clause)
  | localExportListTop
      {item : TopItem} {declaration : ExportDecl}
      {selection : LocalExportList}
      (itemMember : item ∈ module.payload.items)
      (itemShape : item.payload = .exportDecl declaration)
      (modeShape : declaration.payload = .local selection) :
      Occurs module (.localExportList selection)
  | remoteExportSelectionTop
      {item : TopItem} {declaration : ExportDecl}
      {moduleRef : ModuleReference}
      {selection : RemoteExportSelection}
      (itemMember : item ∈ module.payload.items)
      (itemShape : item.payload = .exportDecl declaration)
      (modeShape : declaration.payload = .from moduleRef selection) :
      Occurs module (.remoteExportSelection selection)
  | localExportItem
      {selection : LocalExportList} {entry : ExportEntry}
      {item : ExportItem}
      (selectionOccurs : Occurs module (.localExportList selection))
      (entryMember : entry ∈ selection.payload.entries)
      (entryShape : entry.payload = .item item) :
      Occurs module (.exportItem item)
  | remoteExportItem
      {selection : RemoteExportSelection}
      {entries : List RemoteExportEntry}
      {entry : RemoteExportEntry} {item : ExportItem}
      (selectionOccurs : Occurs module (.remoteExportSelection selection))
      (selectionShape : selection.payload = .braced entries)
      (entryMember : entry ∈ entries)
      (entryShape : entry.payload = .item item) :
      Occurs module (.exportItem item)
  | pragmaTop
      {item : TopItem} {declaration : PragmaDecl}
      (itemMember : item ∈ module.payload.items)
      (itemShape : item.payload = .pragmaDecl declaration) :
      Occurs module (.pragma declaration)
  | topFunctionSignature
      {item : TopItem} {declaration : FunctionDecl}
      (itemMember : item ∈ module.payload.items)
      (itemShape : item.payload = .functionDecl declaration) :
      Occurs module (.signature (some .topLevelFunction)
        .topLevelFunction declaration.payload.signature)
  | topFunctionBody
      {item : TopItem} {declaration : FunctionDecl}
      (itemMember : item ∈ module.payload.items)
      (itemShape : item.payload = .functionDecl declaration) :
      Occurs module (.body 0 declaration.payload.body)
  | classMethodSignature
      {item : TopItem} {declaration : ClassDecl}
      {method : ClassMethodDecl}
      (itemMember : item ∈ module.payload.items)
      (itemShape : item.payload = .classDecl declaration)
      (methodMember : method ∈ declaration.payload.methods) :
      Occurs module (.signature (some .classMethod)
        .classMethod method.payload.signature)
  | instanceMethodSignature
      {item : TopItem} {declaration : InstanceDecl}
      {method : FunctionDecl}
      (itemMember : item ∈ module.payload.items)
      (itemShape : item.payload = .instanceDecl declaration)
      (methodMember : method ∈ declaration.payload.methods) :
      Occurs module (.signature (some .instanceMethod)
        .instanceMethod method.payload.signature)
  | instanceMethodBody
      {item : TopItem} {declaration : InstanceDecl}
      {method : FunctionDecl}
      (itemMember : item ∈ module.payload.items)
      (itemShape : item.payload = .instanceDecl declaration)
      (methodMember : method ∈ declaration.payload.methods) :
      Occurs module (.body 0 method.payload.body)
  | contractFieldInitializer
      {item : TopItem} {declaration : ContractDecl}
      {member : ContractMember} {field : FieldDecl}
      {initializer : Expression}
      (itemMember : item ∈ module.payload.items)
      (itemShape : item.payload = .contractDecl declaration)
      (memberMember : member ∈ declaration.payload.members)
      (memberShape : member.payload = .field field)
      (initializerShape : field.payload.initializer = some initializer) :
      Occurs module (.expression initializer)
  | contractFunctionSignature
      {item : TopItem} {declaration : ContractDecl}
      {member : ContractMember} {functionDeclaration : FunctionDecl}
      (itemMember : item ∈ module.payload.items)
      (itemShape : item.payload = .contractDecl declaration)
      (memberMember : member ∈ declaration.payload.members)
      (memberShape : member.payload = .function functionDeclaration) :
      Occurs module (.signature none .contractFunction
        functionDeclaration.payload.signature)
  | contractFunctionBody
      {item : TopItem} {declaration : ContractDecl}
      {member : ContractMember} {functionDeclaration : FunctionDecl}
      (itemMember : item ∈ module.payload.items)
      (itemShape : item.payload = .contractDecl declaration)
      (memberMember : member ∈ declaration.payload.members)
      (memberShape : member.payload = .function functionDeclaration) :
      Occurs module (.body 0 functionDeclaration.payload.body)
  | fallbackDeclaration
      {item : TopItem} {declaration : ContractDecl}
      {member : ContractMember} {fallbackDeclaration : FallbackDecl}
      (itemMember : item ∈ module.payload.items)
      (itemShape : item.payload = .contractDecl declaration)
      (memberMember : member ∈ declaration.payload.members)
      (memberShape : member.payload = .fallback fallbackDeclaration) :
      Occurs module (.fallback fallbackDeclaration)
  | fallbackBody
      {item : TopItem} {declaration : ContractDecl}
      {member : ContractMember} {fallbackDeclaration : FallbackDecl}
      (itemMember : item ∈ module.payload.items)
      (itemShape : item.payload = .contractDecl declaration)
      (memberMember : member ∈ declaration.payload.members)
      (memberShape : member.payload = .fallback fallbackDeclaration) :
      Occurs module (.body 0 fallbackDeclaration.payload.body)
  | constructorDeclaration
      {item : TopItem} {declaration : ContractDecl}
      {member : ContractMember}
      {constructorDeclaration : ContractConstructorDecl}
      (itemMember : item ∈ module.payload.items)
      (itemShape : item.payload = .contractDecl declaration)
      (memberMember : member ∈ declaration.payload.members)
      (memberShape : member.payload =
        .constructor constructorDeclaration) :
      Occurs module (.contractConstructor constructorDeclaration)
  | constructorBody
      {item : TopItem} {declaration : ContractDecl}
      {member : ContractMember}
      {constructorDeclaration : ContractConstructorDecl}
      (itemMember : item ∈ module.payload.items)
      (itemShape : item.payload = .contractDecl declaration)
      (memberMember : member ∈ declaration.payload.members)
      (memberShape : member.payload =
        .constructor constructorDeclaration) :
      Occurs module (.body 0 constructorDeclaration.payload.body)
  | expressionCallCallee
      {expression callee : Expression} {arguments : List Expression}
      (parent : Occurs module (.expression expression))
      (shape : expression.payload = .call callee arguments) :
      Occurs module (.expression callee)
  | expressionCallArgument
      {expression callee argument : Expression}
      {arguments : List Expression}
      (parent : Occurs module (.expression expression))
      (shape : expression.payload = .call callee arguments)
      (member : argument ∈ arguments) :
      Occurs module (.expression argument)
  | expressionSelectReceiver
      {expression receiver : Expression} {field : IdentifierOccurrence}
      (parent : Occurs module (.expression expression))
      (shape : expression.payload = .select receiver field) :
      Occurs module (.expression receiver)
  | expressionDotConstructorArgument
      {expression argument : Expression} {marker : Located Unit}
      {name : IdentifierOccurrence} {arguments : List Expression}
      (parent : Occurs module (.expression expression))
      (shape : expression.payload =
        .dotConstructor marker name (some arguments))
      (member : argument ∈ arguments) :
      Occurs module (.expression argument)
  | expressionLambdaBody
      {expression : Expression} {parameters : List Parameter}
      {returnType : Option TypeExpr} {body : Body}
      (parent : Occurs module (.expression expression))
      (shape : expression.payload = .lambda parameters returnType body) :
      Occurs module (.body 0 body)
  | expressionAnnotationInner
      {expression inner : Expression} {typeExpression : TypeExpr}
      (parent : Occurs module (.expression expression))
      (shape : expression.payload = .annotation inner typeExpression) :
      Occurs module (.expression inner)
  | expressionKeywordCondition
      {expression condition thenBranch elseBranch : Expression}
      (parent : Occurs module (.expression expression))
      (shape : expression.payload =
        .keywordConditional condition thenBranch elseBranch) :
      Occurs module (.expression condition)
  | expressionKeywordThen
      {expression condition thenBranch elseBranch : Expression}
      (parent : Occurs module (.expression expression))
      (shape : expression.payload =
        .keywordConditional condition thenBranch elseBranch) :
      Occurs module (.expression thenBranch)
  | expressionKeywordElse
      {expression condition thenBranch elseBranch : Expression}
      (parent : Occurs module (.expression expression))
      (shape : expression.payload =
        .keywordConditional condition thenBranch elseBranch) :
      Occurs module (.expression elseBranch)
  | expressionTernaryCondition
      {expression condition thenBranch elseBranch : Expression}
      (parent : Occurs module (.expression expression))
      (shape : expression.payload =
        .ternaryConditional condition thenBranch elseBranch) :
      Occurs module (.expression condition)
  | expressionTernaryThen
      {expression condition thenBranch elseBranch : Expression}
      (parent : Occurs module (.expression expression))
      (shape : expression.payload =
        .ternaryConditional condition thenBranch elseBranch) :
      Occurs module (.expression thenBranch)
  | expressionTernaryElse
      {expression condition thenBranch elseBranch : Expression}
      (parent : Occurs module (.expression expression))
      (shape : expression.payload =
        .ternaryConditional condition thenBranch elseBranch) :
      Occurs module (.expression elseBranch)
  | expressionIndexReceiver
      {expression receiver index : Expression}
      (parent : Occurs module (.expression expression))
      (shape : expression.payload = .index receiver index) :
      Occurs module (.expression receiver)
  | expressionIndexValue
      {expression receiver index : Expression}
      (parent : Occurs module (.expression expression))
      (shape : expression.payload = .index receiver index) :
      Occurs module (.expression index)
  | expressionPrefixOperand
      {expression operand : Expression}
      {operator : Located PrefixOperator}
      (parent : Occurs module (.expression expression))
      (shape : expression.payload = .prefix operator operand) :
      Occurs module (.expression operand)
  | expressionInfixLeft
      {expression left right : Expression}
      {operator : Located InfixOperator}
      (parent : Occurs module (.expression expression))
      (shape : expression.payload = .infix operator left right) :
      Occurs module (.expression left)
  | expressionInfixRight
      {expression left right : Expression}
      {operator : Located InfixOperator}
      (parent : Occurs module (.expression expression))
      (shape : expression.payload = .infix operator left right) :
      Occurs module (.expression right)
  | expressionTupleElement
      {expression element : Expression} {elements : List Expression}
      (parent : Occurs module (.expression expression))
      (shape : expression.payload = .tuple elements)
      (member : element ∈ elements) :
      Occurs module (.expression element)
  | expressionGroupInner
      {expression inner : Expression}
      (parent : Occurs module (.expression expression))
      (shape : expression.payload = .group inner) :
      Occurs module (.expression inner)
  | patternNamedArgument
      {pattern argument : Pattern} {name : QualifiedName}
      {arguments : NonemptyList Pattern}
      (parent : Occurs module (.pattern pattern))
      (shape : pattern.payload = .named name (some arguments))
      (member : argument ∈ arguments.toList) :
      Occurs module (.pattern argument)
  | patternDotConstructorArgument
      {pattern argument : Pattern} {marker : Located Unit}
      {name : IdentifierOccurrence} {arguments : NonemptyList Pattern}
      (parent : Occurs module (.pattern pattern))
      (shape : pattern.payload =
        .dotConstructor marker name (some arguments))
      (member : argument ∈ arguments.toList) :
      Occurs module (.pattern argument)
  | patternComptimeExpression
      {pattern : Pattern} {marker : Marker} {expression : Expression}
      (parent : Occurs module (.pattern pattern))
      (shape : pattern.payload = .comptime marker expression) :
      Occurs module (.expression expression)
  | patternTupleElement
      {pattern element : Pattern} {elements : List Pattern}
      (parent : Occurs module (.pattern pattern))
      (shape : pattern.payload = .tuple elements)
      (member : element ∈ elements) :
      Occurs module (.pattern element)
  | patternGroupInner
      {pattern inner : Pattern}
      (parent : Occurs module (.pattern pattern))
      (shape : pattern.payload = .group inner) :
      Occurs module (.pattern inner)
  | bodyStatement
      {loopDepth : Nat} {body : Body} {statement : Statement}
      (parent : Occurs module (.body loopDepth body))
      (member : statement ∈ body.payload.statements) :
      Occurs module (.statement loopDepth statement)
  | statementAssignmentLeft
      {loopDepth : Nat} {left right : Expression} {statementNode : Statement}
      {operator : Located AssignmentOperator}
      (parent : Occurs module (.statement loopDepth statementNode))
      (shape : statementNode.payload = .assignment operator left right) :
      Occurs module (.expression left)
  | statementAssignmentRight
      {loopDepth : Nat} {left right : Expression}
      {statementNode : Statement}
      {operator : Located AssignmentOperator}
      (parent : Occurs module (.statement loopDepth statementNode))
      (shape : statementNode.payload = .assignment operator left right) :
      Occurs module (.expression right)
  | statementLetInitializer
      {loopDepth : Nat} {statement : Statement}
      {binding : LetBinding} {initializer : Expression}
      (parent : Occurs module (.statement loopDepth statement))
      (shape : statement.payload = .letBinding binding)
      (initializerShape : binding.payload.initializer = some initializer) :
      Occurs module (.expression initializer)
  | statementBlockBody
      {loopDepth : Nat} {statement : Statement} {body : Body}
      (parent : Occurs module (.statement loopDepth statement))
      (shape : statement.payload = .block body) :
      Occurs module (.body loopDepth body)
  | statementExpression
      {loopDepth : Nat} {statement : Statement}
      {expression : Expression} {terminator : Option SourceSpan}
      (parent : Occurs module (.statement loopDepth statement))
      (shape : statement.payload = .expression expression terminator) :
      Occurs module (.expression expression)
  | statementReturnValue
      {loopDepth : Nat} {statement : Statement}
      {expression : Expression} {terminator : SourceSpan}
      (parent : Occurs module (.statement loopDepth statement))
      (shape : statement.payload = .return (some expression) terminator) :
      Occurs module (.expression expression)
  | statementMatchScrutinee
      {loopDepth : Nat} {statement : Statement}
      {scrutinees : NonemptyList Expression}
      {arms : NonemptyList MatchArm} {terminator : Option SourceSpan}
      {scrutinee : Expression}
      (parent : Occurs module (.statement loopDepth statement))
      (shape : statement.payload = .match scrutinees arms terminator)
      (member : scrutinee ∈ scrutinees.toList) :
      Occurs module (.expression scrutinee)
  | statementMatchPattern
      {loopDepth : Nat} {statement : Statement}
      {scrutinees : NonemptyList Expression}
      {arms : NonemptyList MatchArm} {terminator : Option SourceSpan}
      {arm : MatchArm} {pattern : Pattern}
      (parent : Occurs module (.statement loopDepth statement))
      (shape : statement.payload = .match scrutinees arms terminator)
      (armMember : arm ∈ arms.toList)
      (patternMember : pattern ∈ arm.payload.patterns.toList) :
      Occurs module (.pattern pattern)
  | statementMatchArmBody
      {loopDepth : Nat} {statement : Statement}
      {scrutinees : NonemptyList Expression}
      {arms : NonemptyList MatchArm} {terminator : Option SourceSpan}
      {arm : MatchArm}
      (parent : Occurs module (.statement loopDepth statement))
      (shape : statement.payload = .match scrutinees arms terminator)
      (armMember : arm ∈ arms.toList) :
      Occurs module (.body loopDepth arm.payload.body)
  | statementIfCondition
      {loopDepth : Nat} {statement : Statement}
      {condition : Expression} {thenBody : Body} {elseBody : Option Body}
      (parent : Occurs module (.statement loopDepth statement))
      (shape : statement.payload =
        .ifThenElse condition thenBody elseBody) :
      Occurs module (.expression condition)
  | statementIfThenBody
      {loopDepth : Nat} {statement : Statement}
      {condition : Expression} {thenBody : Body} {elseBody : Option Body}
      (parent : Occurs module (.statement loopDepth statement))
      (shape : statement.payload =
        .ifThenElse condition thenBody elseBody) :
      Occurs module (.body loopDepth thenBody)
  | statementIfElseBody
      {loopDepth : Nat} {statement : Statement}
      {condition : Expression} {thenBody elseBody : Body}
      (parent : Occurs module (.statement loopDepth statement))
      (shape : statement.payload =
        .ifThenElse condition thenBody (some elseBody)) :
      Occurs module (.body loopDepth elseBody)
  | statementForInitializer
      {loopDepth : Nat} {statement : Statement}
      {initializers : List ForInitItem} {condition : Expression}
      {post : List ForPostItem} {body : Body} {item : ForInitItem}
      (parent : Occurs module (.statement loopDepth statement))
      (shape : statement.payload =
        .forLoop initializers condition post body)
      (member : item ∈ initializers) :
      Occurs module (.forInit item)
  | statementForCondition
      {loopDepth : Nat} {statement : Statement}
      {initializers : List ForInitItem} {condition : Expression}
      {post : List ForPostItem} {body : Body}
      (parent : Occurs module (.statement loopDepth statement))
      (shape : statement.payload =
        .forLoop initializers condition post body) :
      Occurs module (.expression condition)
  | statementForPost
      {loopDepth : Nat} {statement : Statement}
      {initializers : List ForInitItem} {condition : Expression}
      {post : List ForPostItem} {body : Body} {item : ForPostItem}
      (parent : Occurs module (.statement loopDepth statement))
      (shape : statement.payload =
        .forLoop initializers condition post body)
      (member : item ∈ post) :
      Occurs module (.forPost item)
  | statementForBody
      {loopDepth : Nat} {statement : Statement}
      {initializers : List ForInitItem} {condition : Expression}
      {post : List ForPostItem} {body : Body}
      (parent : Occurs module (.statement loopDepth statement))
      (shape : statement.payload =
        .forLoop initializers condition post body) :
      Occurs module (.body (loopDepth + 1) body)
  | forInitLetInitializer
      {item : ForInitItem} {binding : LetBinding}
      {initializer : Expression}
      (parent : Occurs module (.forInit item))
      (shape : item.payload = .letBinding binding)
      (initializerShape : binding.payload.initializer = some initializer) :
      Occurs module (.expression initializer)
  | forInitAssignmentLeft
      {item : ForInitItem} {left right : Expression}
      {operator : Located AssignmentOperator}
      (parent : Occurs module (.forInit item))
      (shape : item.payload = .assignment operator left right) :
      Occurs module (.expression left)
  | forInitAssignmentRight
      {item : ForInitItem} {left right : Expression}
      {operator : Located AssignmentOperator}
      (parent : Occurs module (.forInit item))
      (shape : item.payload = .assignment operator left right) :
      Occurs module (.expression right)
  | forInitExpression
      {item : ForInitItem} {expression : Expression}
      (parent : Occurs module (.forInit item))
      (shape : item.payload = .expression expression) :
      Occurs module (.expression expression)
  | forPostAssignmentLeft
      {item : ForPostItem} {left right : Expression}
      {operator : Located AssignmentOperator}
      (parent : Occurs module (.forPost item))
      (shape : item.payload = .assignment operator left right) :
      Occurs module (.expression left)
  | forPostAssignmentRight
      {item : ForPostItem} {left right : Expression}
      {operator : Located AssignmentOperator}
      (parent : Occurs module (.forPost item))
      (shape : item.payload = .assignment operator left right) :
      Occurs module (.expression right)
  | forPostExpression
      {item : ForPostItem} {expression : Expression}
      (parent : Occurs module (.forPost item))
      (shape : item.payload = .expression expression) :
      Occurs module (.expression expression)

/-- Invert an import-selection occurrence back to its top-level declaration. -/
theorem Occurs.importSelection_inversion
    {module : ParsedModuleV1} {selection : ImportSelection}
    (occurrence : Occurs module (.importSelection selection)) :
    ∃ item declaration hidingClause,
      item ∈ module.payload.items ∧
        item.payload = .importDecl declaration ∧
        declaration.payload.mode = .items selection hidingClause := by
  cases occurrence with
  | importSelectionTop itemMember itemShape modeShape =>
      exact ⟨_, _, _, itemMember, itemShape, modeShape⟩

/-- Invert a hiding-clause occurrence back to its top-level declaration. -/
theorem Occurs.hidingClause_inversion
    {module : ParsedModuleV1} {clause : HidingClause}
    (occurrence : Occurs module (.hidingClause clause)) :
    ∃ item declaration selection,
      item ∈ module.payload.items ∧
        item.payload = .importDecl declaration ∧
        declaration.payload.mode = .items selection (some clause) := by
  cases occurrence with
  | hidingClauseTop itemMember itemShape modeShape =>
      exact ⟨_, _, _, itemMember, itemShape, modeShape⟩

/-- Invert a pragma occurrence back to its top-level item. -/
theorem Occurs.pragma_inversion
    {module : ParsedModuleV1} {declaration : PragmaDecl}
    (occurrence : Occurs module (.pragma declaration)) :
    ∃ item,
      item ∈ module.payload.items ∧
        item.payload = .pragmaDecl declaration := by
  cases occurrence with
  | pragmaTop itemMember itemShape =>
      exact ⟨_, itemMember, itemShape⟩

/-- A lambda body always begins a fresh loop-control region. -/
theorem Occurs.lambdaBody
    {module : ParsedModuleV1} {expression : Expression}
    {parameters : List Parameter} {returnType : Option TypeExpr} {body : Body}
    (parent : Occurs module (.expression expression))
    (shape : expression.payload = .lambda parameters returnType body) :
    Occurs module (.body 0 body) :=
  Occurs.expressionLambdaBody parent shape

/-- Only the body of a `for` statement receives the incremented loop depth. -/
theorem Occurs.forBody
    {module : ParsedModuleV1} {loopDepth : Nat} {statement : Statement}
    {initializers : List ForInitItem} {condition : Expression}
    {post : List ForPostItem} {body : Body}
    (parent : Occurs module (.statement loopDepth statement))
    (shape : statement.payload = .forLoop initializers condition post body) :
    Occurs module (.body (loopDepth + 1) body) :=
  Occurs.statementForBody parent shape

end StructuralSite

namespace StructuralDiagnostic

/-- Wildcard marker spans written in an import selection. -/
def importWildcardSpans
    (entries : List ImportSelectorEntry) : List SourceSpan :=
  entries.filterMap fun entry =>
    match entry.payload with
    | .wildcard marker => some marker.span
    | .named _ _ => none

/-- Named import entries paired with their effective local names. -/
def namedImportBindings
    (entries : List ImportSelectorEntry) :
    List (IdentifierOccurrence × IdentifierOccurrence) :=
  entries.filterMap fun entry =>
    match entry.payload with
    | .wildcard _ => none
    | .named source alias => some (source, alias.getD source)

/-- Wildcard marker spans written in a local export list. -/
def localExportWildcardSpans
    (entries : List ExportEntry) : List SourceSpan :=
  entries.filterMap fun entry =>
    match entry.payload with
    | .wildcard marker => some marker.span
    | .item _ | .allFrom _ _ => none

/-- Named export items written in a local export list. -/
def localExportItems (entries : List ExportEntry) : List ExportItem :=
  entries.filterMap fun entry =>
    match entry.payload with
    | .item item => some item
    | .wildcard _ | .allFrom _ _ => none

/-- Module references written in local `all-from` export entries. -/
def localExportReferences
    (entries : List ExportEntry) : List ModuleReference :=
  entries.filterMap fun entry =>
    match entry.payload with
    | .allFrom reference _ => some reference
    | .wildcard _ | .item _ => none

/-- Wildcard marker spans written in a braced remote export selection. -/
def remoteExportWildcardSpans
    (entries : List RemoteExportEntry) : List SourceSpan :=
  entries.filterMap fun entry =>
    match entry.payload with
    | .wildcard marker => some marker.span
    | .item _ => none

/-- Named export items written in a braced remote export selection. -/
def remoteExportItems
    (entries : List RemoteExportEntry) : List ExportItem :=
  entries.filterMap fun entry =>
    match entry.payload with
    | .item item => some item
    | .wildcard _ => none

/-- A signature marker selected by either modifier position. -/
inductive SignatureModifierIn
    (signature : FunctionSignature) : Marker → Prop where
  | publicMarker {marker : Marker}
      (selected : signature.payload.public = some marker) :
      SignatureModifierIn signature marker
  | payableMarker {marker : Marker}
      (selected : signature.payload.payable = some marker) :
      SignatureModifierIn signature marker

/--
Declarative applicability of a structural diagnostic to a parsed module.
Each rule names the AST site and the local structural fact that gives rise to
the diagnostic; it does not call the executable structural validator.
-/
inductive Applies (module : ParsedModuleV1) : StructuralDiagnostic → Prop where
  | emptyImportSelection
      {selection : ImportSelection}
      (occurrence : StructuralSite.Occurs module
        (.importSelection selection))
      (empty : selection.payload.entries = []) :
      Applies module (.emptyImportSelection selection.span)
  | mixedImportWildcard
      {selection : ImportSelection} {span : SourceSpan}
      (occurrence : StructuralSite.Occurs module
        (.importSelection selection))
      (mixed : selection.payload.entries.length ≠ 1)
      (least : LeastSpanIn span
        (importWildcardSpans selection.payload.entries)) :
      Applies module (.mixedImportWildcard span)
  | duplicateImportSourceName
      {selection : ImportSelection}
      {binding : IdentifierOccurrence × IdentifierOccurrence}
      (occurrence : StructuralSite.Occurs module
        (.importSelection selection))
      (duplicate : LaterDuplicate
        (namedImportBindings selection.payload.entries)
        (fun value => value.1.payload) binding) :
      Applies module
        (.duplicateImportSourceName binding.1.span binding.1.payload)
  | duplicateImportLocalName
      {selection : ImportSelection}
      {binding : IdentifierOccurrence × IdentifierOccurrence}
      (occurrence : StructuralSite.Occurs module
        (.importSelection selection))
      (duplicate : LaterDuplicate
        (namedImportBindings selection.payload.entries)
        (fun value => value.2.payload) binding) :
      Applies module
        (.duplicateImportLocalName binding.2.span binding.2.payload)
  | emptyHidingClause
      {clause : HidingClause}
      (occurrence : StructuralSite.Occurs module (.hidingClause clause))
      (empty : clause.payload.names = []) :
      Applies module (.emptyHidingClause clause.span)
  | duplicateHiddenName
      {clause : HidingClause} {name : IdentifierOccurrence}
      (occurrence : StructuralSite.Occurs module (.hidingClause clause))
      (duplicate : LaterDuplicate clause.payload.names
        (fun value => value.payload) name) :
      Applies module (.duplicateHiddenName name.span name.payload)
  | emptyLocalExportList
      {selection : LocalExportList}
      (occurrence : StructuralSite.Occurs module
        (.localExportList selection))
      (empty : selection.payload.entries = []) :
      Applies module (.emptyLocalExportList selection.span)
  | emptyRemoteExportList
      {selection : RemoteExportSelection}
      (entries : List RemoteExportEntry)
      (occurrence : StructuralSite.Occurs module
        (.remoteExportSelection selection))
      (braced : selection.payload = .braced entries)
      (empty : entries = []) :
      Applies module (.emptyRemoteExportList selection.span)
  | mixedLocalExportWildcard
      {selection : LocalExportList} {span : SourceSpan}
      (occurrence : StructuralSite.Occurs module
        (.localExportList selection))
      (mixed : selection.payload.entries.length ≠ 1)
      (least : LeastSpanIn span
        (localExportWildcardSpans selection.payload.entries)) :
      Applies module (.mixedExportWildcard span)
  | mixedRemoteExportWildcard
      {selection : RemoteExportSelection}
      {entries : List RemoteExportEntry} {span : SourceSpan}
      (occurrence : StructuralSite.Occurs module
        (.remoteExportSelection selection))
      (braced : selection.payload = .braced entries)
      (mixed : entries.length ≠ 1)
      (least : LeastSpanIn span (remoteExportWildcardSpans entries)) :
      Applies module (.mixedExportWildcard span)
  | duplicateLocalExportName
      {selection : LocalExportList} {item : ExportItem}
      (occurrence : StructuralSite.Occurs module
        (.localExportList selection))
      (duplicate : LaterDuplicate
        (localExportItems selection.payload.entries)
        (fun value => value.payload.name.payload) item) :
      Applies module
        (.duplicateExportName item.payload.name.span
          item.payload.name.payload)
  | duplicateRemoteExportName
      {selection : RemoteExportSelection}
      {entries : List RemoteExportEntry} {item : ExportItem}
      (occurrence : StructuralSite.Occurs module
        (.remoteExportSelection selection))
      (braced : selection.payload = .braced entries)
      (duplicate : LaterDuplicate (remoteExportItems entries)
        (fun value => value.payload.name.payload) item) :
      Applies module
        (.duplicateExportName item.payload.name.span
          item.payload.name.payload)
  | duplicateExportModuleReference
      {selection : LocalExportList} {reference : ModuleReference}
      (occurrence : StructuralSite.Occurs module
        (.localExportList selection))
      (duplicate : LaterDuplicate
        (localExportReferences selection.payload.entries)
        ModuleReference.eraseLocations reference) :
      Applies module
        (.duplicateExportModuleReference reference.span
          reference.eraseLocations)
  | duplicateExportConstructor
      {item : ExportItem} {selection : ConstructorSelection}
      {constructors : NonemptyList IdentifierOccurrence}
      {name : IdentifierOccurrence}
      (occurrence : StructuralSite.Occurs module (.exportItem item))
      (selectionPresent : item.payload.constructors = some selection)
      (named : selection.payload = .named constructors)
      (duplicate : LaterDuplicate constructors.toList
        (fun value => value.payload) name) :
      Applies module (.duplicateExportConstructor name.span name.payload)
  | matchPatternArityMismatch
      {loopDepth : Nat} {statement : Statement}
      {scrutinees : NonemptyList Expression}
      {arms : NonemptyList MatchArm} {terminator : Option SourceSpan}
      {arm : MatchArm}
      (occurrence : StructuralSite.Occurs module
        (.statement loopDepth statement))
      (shape : statement.payload = .match scrutinees arms terminator)
      (armMember : arm ∈ arms.toList)
      (mismatch : arm.payload.patterns.toList.length ≠
        scrutinees.toList.length) :
      Applies module (.matchPatternArityMismatch arm.span
        scrutinees.toList.length arm.payload.patterns.toList.length)
  | emptyGenericPragmaTargets
      {declaration : PragmaDecl}
      (occurrence : StructuralSite.Occurs module (.pragma declaration))
      (kind : declaration.payload.kind.payload = .noGenericInstanceFor)
      (empty : declaration.payload.targets = []) :
      Applies module
        (.emptyGenericPragmaTargets declaration.payload.kind.span)
  | duplicatePragmaTarget
      {declaration : PragmaDecl} {target : IdentifierOccurrence}
      (occurrence : StructuralSite.Occurs module (.pragma declaration))
      (duplicate : LaterDuplicate declaration.payload.targets
        (fun value => value.payload) target) :
      Applies module (.duplicatePragmaTarget target.span target.payload)
  | signatureModifierNotAllowed
      {context : ModifierContext} {parameterContext : ParameterContext}
      {signature : FunctionSignature} {marker : Marker}
      (occurrence : StructuralSite.Occurs module
        (.signature (some context) parameterContext signature))
      (selected : SignatureModifierIn signature marker) :
      Applies module (.modifierNotAllowed marker.span context marker.payload)
  | fallbackModifierNotAllowed
      {declaration : FallbackDecl} {marker : Marker}
      (occurrence : StructuralSite.Occurs module (.fallback declaration))
      (selected : declaration.payload.public = some marker) :
      Applies module
        (.modifierNotAllowed marker.span .fallback marker.payload)
  | constructorModifierNotAllowed
      {declaration : ContractConstructorDecl} {marker : Marker}
      (occurrence : StructuralSite.Occurs module
        (.contractConstructor declaration))
      (selected : declaration.payload.public = some marker) :
      Applies module
        (.modifierNotAllowed marker.span .contractConstructor marker.payload)
  | fallbackHasParameters
      {declaration : FallbackDecl}
      (occurrence : StructuralSite.Occurs module (.fallback declaration))
      (nonempty : declaration.payload.parameters ≠ []) :
      Applies module (.fallbackHasParameters declaration.payload.marker.span
        declaration.payload.parameters.length)
  | fallbackHasNonUnitReturn
      {declaration : FallbackDecl} {returnType : TypeExpr}
      (occurrence : StructuralSite.Occurs module (.fallback declaration))
      (returnPresent : declaration.payload.returnType = some returnType)
      (notUnit : ¬GroupedUnit returnType) :
      Applies module (.fallbackHasNonUnitReturn returnType.span)
  | signatureParameterTypeMissing
      {modifierContext : Option ModifierContext}
      {parameterContext : ParameterContext}
      {signature : FunctionSignature} {parameter : Parameter}
      (occurrence : StructuralSite.Occurs module
        (.signature modifierContext parameterContext signature))
      (member : parameter ∈ signature.payload.parameters)
      (missing : parameter.payload.type = none) :
      Applies module (.requiredParameterTypeMissing
        parameter.payload.name.span parameterContext)
  | constructorParameterTypeMissing
      {declaration : ContractConstructorDecl} {parameter : Parameter}
      (occurrence : StructuralSite.Occurs module
        (.contractConstructor declaration))
      (member : parameter ∈ declaration.payload.parameters)
      (missing : parameter.payload.type = none) :
      Applies module (.requiredParameterTypeMissing
        parameter.payload.name.span .contractConstructor)
  | breakOutsideLoop
      {statement : Statement} {terminator : SourceSpan}
      (occurrence : StructuralSite.Occurs module (.statement 0 statement))
      (shape : statement.payload = .break terminator) :
      Applies module (.controlOutsideLoop statement.span .breakControl)
  | continueOutsideLoop
      {statement : Statement} {terminator : SourceSpan}
      (occurrence : StructuralSite.Occurs module (.statement 0 statement))
      (shape : statement.payload = .continue terminator) :
      Applies module (.controlOutsideLoop statement.span .continueControl)

/-- Every applicable diagnostic is justified by a reached structural site. -/
theorem Applies.hasSite
    {module : ParsedModuleV1} {diagnostic : StructuralDiagnostic}
    (applies : Applies module diagnostic) :
    ∃ site, StructuralSite.Occurs module site := by
  cases applies <;> exact ⟨_, by assumption⟩

/-- Characterization of an empty import-selection diagnostic. -/
@[simp] theorem applies_emptyImportSelection_iff
    {module : ParsedModuleV1} {span : SourceSpan} :
    Applies module (.emptyImportSelection span) ↔
      ∃ selection : ImportSelection,
        StructuralSite.Occurs module (.importSelection selection) ∧
          selection.span = span ∧ selection.payload.entries = [] := by
  constructor
  · intro applies
    cases applies with
    | emptyImportSelection occurrence empty =>
        exact ⟨_, occurrence, rfl, empty⟩
  · rintro ⟨selection, occurrence, spanEq, empty⟩
    subst span
    exact .emptyImportSelection occurrence empty

/-- Characterization of a fallback-parameter diagnostic. -/
@[simp] theorem applies_fallbackHasParameters_iff
    {module : ParsedModuleV1} {span : SourceSpan} {count : Nat} :
    Applies module (.fallbackHasParameters span count) ↔
      ∃ declaration : FallbackDecl,
        StructuralSite.Occurs module (.fallback declaration) ∧
          declaration.payload.marker.span = span ∧
          declaration.payload.parameters.length = count ∧
          declaration.payload.parameters ≠ [] := by
  constructor
  · intro applies
    cases applies with
    | fallbackHasParameters occurrence nonempty =>
        exact ⟨_, occurrence, rfl, rfl, nonempty⟩
  · rintro ⟨declaration, occurrence, spanEq, countEq, nonempty⟩
    subst span
    subst count
    exact .fallbackHasParameters occurrence nonempty

/-- Characterization of a fallback return-type diagnostic. -/
@[simp] theorem applies_fallbackHasNonUnitReturn_iff
    {module : ParsedModuleV1} {span : SourceSpan} :
    Applies module (.fallbackHasNonUnitReturn span) ↔
      ∃ declaration : FallbackDecl, ∃ returnType : TypeExpr,
        StructuralSite.Occurs module (.fallback declaration) ∧
          declaration.payload.returnType = some returnType ∧
          returnType.span = span ∧ ¬GroupedUnit returnType := by
  constructor
  · intro applies
    cases applies with
    | fallbackHasNonUnitReturn occurrence returnPresent notUnit =>
        exact ⟨_, _, occurrence, returnPresent, rfl, notUnit⟩
  · rintro ⟨declaration, returnType, occurrence, returnPresent,
      spanEq, notUnit⟩
    subst span
    exact .fallbackHasNonUnitReturn occurrence returnPresent notUnit

/-- Inversion of a loop-control diagnostic into the corresponding statement. -/
theorem applies_controlOutsideLoop_iff
    {module : ParsedModuleV1} {span : SourceSpan} {control : ControlKind} :
    Applies module (.controlOutsideLoop span control) ↔
      (control = .breakControl ∧
        ∃ statement terminator,
          StructuralSite.Occurs module (.statement 0 statement) ∧
            statement.span = span ∧ statement.payload = .break terminator) ∨
      (control = .continueControl ∧
        ∃ statement terminator,
          StructuralSite.Occurs module (.statement 0 statement) ∧
            statement.span = span ∧
            statement.payload = .continue terminator) := by
  constructor
  · intro applies
    cases applies with
    | breakOutsideLoop occurrence shape =>
        exact Or.inl ⟨rfl, _, _, occurrence, rfl, shape⟩
    | continueOutsideLoop occurrence shape =>
        exact Or.inr ⟨rfl, _, _, occurrence, rfl, shape⟩
  · intro witness
    rcases witness with
      ⟨controlEq, statement, terminator, occurrence, spanEq, shape⟩ |
      ⟨controlEq, statement, terminator, occurrence, spanEq, shape⟩
    · subst control
      subst span
      exact .breakOutsideLoop occurrence shape
    · subst control
      subst span
      exact .continueOutsideLoop occurrence shape

end StructuralDiagnostic

/-- A finite list has at least one written element. -/
def HasElement {α : Type} (values : List α) : Prop :=
  ∃ value, value ∈ values

@[simp] theorem hasElement_nil {α : Type} :
    ¬HasElement ([] : List α) := by
  simp [HasElement]

@[simp] theorem hasElement_cons {α : Type} (head : α) (tail : List α) :
    HasElement (head :: tail) := by
  exact ⟨head, by simp⟩

/-- Any list known not to be empty has a written element. -/
theorem HasElement.of_ne_nil {α : Type} {values : List α}
    (notEmpty : values ≠ []) : HasElement values := by
  cases values with
  | nil => exact False.elim (notEmpty rfl)
  | cons head tail => exact hasElement_cons head tail

/-- The keys of a finite list are pairwise distinct. -/
def UniqueBy {α κ : Type} (key : α → κ) (values : List α) : Prop :=
  (values.map key).Nodup

/-- A unique-key list cannot contain a later duplicate occurrence. -/
theorem UniqueBy.not_laterDuplicate
    {α κ : Type} {key : α → κ} {values : List α} {later : α}
    (unique : UniqueBy key values)
    (duplicate : LaterDuplicate values key later) : False := by
  induction values with
  | nil => simp [LaterDuplicate] at duplicate
  | cons head tail induction =>
      rw [laterDuplicate_cons_iff] at duplicate
      rw [UniqueBy, List.map_cons, List.nodup_cons] at unique
      rcases unique with ⟨headAbsent, tailUnique⟩
      rcases duplicate with suffixDuplicate |
          ⟨candidate, member, candidateEq, keyEq⟩
      · exact induction tailUnique suffixDuplicate
      · apply headAbsent
        apply List.mem_map.mpr
        exact ⟨candidate, member, keyEq.symm⟩

/-- Failure of finite key uniqueness supplies a concrete later duplicate. -/
theorem UniqueBy.failure_witness
    {α κ : Type} [DecidableEq κ]
    {key : α → κ} {values : List α}
    (notUnique : ¬UniqueBy key values) :
    ∃ later, LaterDuplicate values key later := by
  induction values with
  | nil =>
      exact False.elim (notUnique (by simp [UniqueBy]))
  | cons head tail induction =>
      rw [UniqueBy, List.map_cons, List.nodup_cons] at notUnique
      by_cases headRepeated : key head ∈ tail.map key
      · rcases List.mem_map.mp headRepeated with
          ⟨candidate, member, keyEq⟩
        exact ⟨candidate,
          LaterDuplicate.of_head member rfl keyEq.symm⟩
      · have tailNotUnique : ¬UniqueBy key tail := by
          intro tailUnique
          exact notUnique ⟨headRepeated, tailUnique⟩
        rcases induction tailNotUnique with ⟨later, duplicate⟩
        exact ⟨later, LaterDuplicate.of_tail duplicate⟩

/-- Absence of every concrete later duplicate establishes key uniqueness. -/
theorem UniqueBy.of_no_laterDuplicate
    {α κ : Type} [DecidableEq κ]
    {key : α → κ} {values : List α}
    (noneLater : ∀ later, ¬LaterDuplicate values key later) :
    UniqueBy key values := by
  by_cases unique : UniqueBy key values
  · exact unique
  · rcases UniqueBy.failure_witness unique with ⟨later, duplicate⟩
    exact False.elim (noneLater later duplicate)

/-- Strict span order is transitive. -/
theorem SpanBefore.trans
    {left middle right : SourceSpan}
    (leftMiddle : SpanBefore left middle)
    (middleRight : SpanBefore middle right) :
    SpanBefore left right := by
  rcases leftMiddle with sourceLeftMiddle |
      ⟨sameSourceLeftMiddle, positionLeftMiddle⟩
  · rcases middleRight with sourceMiddleRight |
        ⟨sameSourceMiddleRight, positionMiddleRight⟩
    · exact SpanBefore.of_source
        (Std.TransCmp.lt_trans sourceLeftMiddle sourceMiddleRight)
    · apply SpanBefore.of_source
      rw [← sameSourceMiddleRight]
      exact sourceLeftMiddle
  · rcases middleRight with sourceMiddleRight |
        ⟨sameSourceMiddleRight, positionMiddleRight⟩
    · apply SpanBefore.of_source
      rw [sameSourceLeftMiddle]
      exact sourceMiddleRight
    · refine Or.inr ⟨sameSourceLeftMiddle.trans sameSourceMiddleRight, ?_⟩
      rcases positionLeftMiddle with startLeftMiddle |
          ⟨sameStartLeftMiddle, endLeftMiddle⟩
      · rcases positionMiddleRight with startMiddleRight |
            ⟨sameStartMiddleRight, endMiddleRight⟩
        · exact Or.inl (Nat.lt_trans startLeftMiddle startMiddleRight)
        · apply Or.inl
          rw [← sameStartMiddleRight]
          exact startLeftMiddle
      · rcases positionMiddleRight with startMiddleRight |
            ⟨sameStartMiddleRight, endMiddleRight⟩
        · apply Or.inl
          rw [sameStartLeftMiddle]
          exact startMiddleRight
        · exact Or.inr ⟨sameStartLeftMiddle.trans sameStartMiddleRight,
            Nat.lt_trans endLeftMiddle endMiddleRight⟩

/-- Every finite nonempty span list contains a least listed span. -/
theorem exists_leastSpanIn_of_hasElement
    (spans : List SourceSpan) (hasElement : HasElement spans) :
    ∃ span, LeastSpanIn span spans := by
  induction spans with
  | nil => exact False.elim (hasElement_nil hasElement)
  | cons head tail induction =>
      cases tail with
      | nil => exact ⟨head, leastSpanIn_singleton head⟩
      | cons next rest =>
          have tailHasElement : HasElement (next :: rest) :=
            hasElement_cons next rest
          rcases induction tailHasElement with ⟨least, leastInTail⟩
          by_cases headBefore : SpanBefore head least
          · refine ⟨head, ?_⟩
            constructor
            · simp
            · rw [noSpanBefore_iff]
              intro candidate member candidateBefore
              rcases List.mem_cons.mp member with equal | tailMember
              · subst candidate
                exact spanBefore_self head candidateBefore
              · exact leastInTail.not_before tailMember
                  (SpanBefore.trans candidateBefore headBefore)
          · refine ⟨least, ?_⟩
            constructor
            · exact List.mem_cons_of_mem head leastInTail.member
            · rw [noSpanBefore_iff]
              intro candidate member
              rcases List.mem_cons.mp member with equal | tailMember
              · subst candidate
                exact headBefore
              · exact leastInTail.not_before tailMember

/-- A wildcard is valid alone, or the finite entry list has no wildcard. -/
def WildcardListShape
    (entryCount : Nat) (wildcardSpans : List SourceSpan) : Prop :=
  entryCount = 1 ∨ wildcardSpans = []

/-- A valid wildcard shape cannot yield a mixed-wildcard diagnostic. -/
theorem WildcardListShape.not_mixed_least
    {entryCount : Nat} {wildcardSpans : List SourceSpan}
    {span : SourceSpan}
    (shape : WildcardListShape entryCount wildcardSpans)
    (mixed : entryCount ≠ 1)
    (least : LeastSpanIn span wildcardSpans) : False := by
  rcases shape with countOne | noWildcard
  · exact mixed countOne
  · have member := least.member
    simp [noWildcard] at member

/-- No mixed-wildcard witness establishes the accepted wildcard-list shape. -/
theorem WildcardListShape.of_no_mixed_least
    {entryCount : Nat} {wildcardSpans : List SourceSpan}
    (noMixed : ∀ span,
      entryCount ≠ 1 → LeastSpanIn span wildcardSpans → False) :
    WildcardListShape entryCount wildcardSpans := by
  by_cases countOne : entryCount = 1
  · exact Or.inl countOne
  · apply Or.inr
    by_cases empty : wildcardSpans = []
    · exact empty
    · have hasElement : HasElement wildcardSpans :=
        HasElement.of_ne_nil empty
      rcases exists_leastSpanIn_of_hasElement wildcardSpans hasElement with
        ⟨least, leastProof⟩
      exact False.elim (noMixed least countOne leastProof)

namespace StructuralSite

/-- Every parameter in the finite list carries an explicit type. -/
def ParameterTypesPresent (parameters : List Parameter) : Prop :=
  ∀ parameter ∈ parameters,
    ∃ typeExpression, parameter.payload.type = some typeExpression

/-- Modifier positions accepted for the declaration context of a signature. -/
def SignatureModifiersAllowed
    (context : Option ModifierContext)
    (signature : FunctionSignature) : Prop :=
  match context with
  | none => True
  | some _ =>
      signature.payload.public = none ∧ signature.payload.payable = none

/-- A wildcard selection and a named constructor list are both well formed. -/
def ConstructorSelectionAccepts : Option ConstructorSelection → Prop
  | none => True
  | some selection =>
      match selection.payload with
      | .all _ => True
      | .named constructors =>
          UniqueBy (fun name => name.payload) constructors.toList

/-- The target requirement attached to one pragma kind. -/
def PragmaTargetsPresentWhenRequired (declaration : PragmaDecl) : Prop :=
  match declaration.payload.kind.payload with
  | .noGenericInstanceFor => HasElement declaration.payload.targets
  | .noCoverageCondition
  | .noPattersonCondition
  | .noBoundedVariableCondition => True

/-- A fallback return is absent or is unit after removing explicit groups. -/
def FallbackReturnAccepts : Option TypeExpr → Prop
  | none => True
  | some returnType => GroupedUnit returnType

/-- Every match arm has one pattern for each scrutinee. -/
def MatchAritiesAgree
    (scrutinees : NonemptyList Expression)
    (arms : NonemptyList MatchArm) : Prop :=
  ∀ arm ∈ arms.toList,
    arm.payload.patterns.toList.length = scrutinees.toList.length

/-- The local well-formedness conditions for one reached structural site. -/
def Accepts : StructuralSite → Prop
  | .importSelection selection =>
      HasElement selection.payload.entries ∧
        WildcardListShape selection.payload.entries.length
          (StructuralDiagnostic.importWildcardSpans
            selection.payload.entries) ∧
        UniqueBy (fun binding => binding.1.payload)
          (StructuralDiagnostic.namedImportBindings
            selection.payload.entries) ∧
        UniqueBy (fun binding => binding.2.payload)
          (StructuralDiagnostic.namedImportBindings
            selection.payload.entries)
  | .hidingClause clause =>
      HasElement clause.payload.names ∧
        UniqueBy (fun name => name.payload) clause.payload.names
  | .localExportList selection =>
      HasElement selection.payload.entries ∧
        WildcardListShape selection.payload.entries.length
          (StructuralDiagnostic.localExportWildcardSpans
            selection.payload.entries) ∧
        UniqueBy (fun item => item.payload.name.payload)
          (StructuralDiagnostic.localExportItems
            selection.payload.entries) ∧
        UniqueBy ModuleReference.eraseLocations
          (StructuralDiagnostic.localExportReferences
            selection.payload.entries)
  | .remoteExportSelection selection =>
      match selection.payload with
      | .dotWildcard _ => True
      | .braced entries =>
          HasElement entries ∧
            WildcardListShape entries.length
              (StructuralDiagnostic.remoteExportWildcardSpans entries) ∧
            UniqueBy (fun item => item.payload.name.payload)
              (StructuralDiagnostic.remoteExportItems entries)
  | .exportItem item =>
      ConstructorSelectionAccepts item.payload.constructors
  | .pragma declaration =>
      PragmaTargetsPresentWhenRequired declaration ∧
        UniqueBy (fun target => target.payload)
          declaration.payload.targets
  | .signature modifierContext _parameterContext functionSignature =>
      SignatureModifiersAllowed modifierContext functionSignature ∧
        ParameterTypesPresent functionSignature.payload.parameters
  | .fallback declaration =>
      declaration.payload.public = none ∧
        declaration.payload.parameters = [] ∧
        FallbackReturnAccepts declaration.payload.returnType
  | .contractConstructor declaration =>
      declaration.payload.public = none ∧
        ParameterTypesPresent declaration.payload.parameters
  | .statement loopDepth statementNode =>
      match statementNode.payload with
      | .match scrutinees arms _ => MatchAritiesAgree scrutinees arms
      | .break _ | .continue _ => 0 < loopDepth
      | _ => True
  | .expression _ | .pattern _ | .body _ _ | .forInit _ | .forPost _ =>
      True

@[simp] theorem accepts_expression (expression : Expression) :
    Accepts (.expression expression) :=
  True.intro

@[simp] theorem accepts_pattern (pattern : Pattern) :
    Accepts (.pattern pattern) :=
  True.intro

@[simp] theorem accepts_body (loopDepth : Nat) (body : Body) :
    Accepts (.body loopDepth body) :=
  True.intro

@[simp] theorem accepts_forInit (item : ForInitItem) :
    Accepts (.forInit item) :=
  True.intro

@[simp] theorem accepts_forPost (item : ForPostItem) :
    Accepts (.forPost item) :=
  True.intro

@[simp] theorem accepts_remoteDotWildcard
    (span : SourceSpan) (marker : Marker) :
    Accepts (.remoteExportSelection
      (show RemoteExportSelection from ⟨span, .dotWildcard marker⟩)) :=
  True.intro

@[simp] theorem accepts_break_iff
    (loopDepth : Nat) (span terminator : SourceSpan) :
    Accepts (.statement loopDepth
      (show Statement from ⟨span, .break terminator⟩)) ↔
        0 < loopDepth :=
  Iff.rfl

@[simp] theorem accepts_continue_iff
    (loopDepth : Nat) (span terminator : SourceSpan) :
    Accepts (.statement loopDepth
      (show Statement from ⟨span, .continue terminator⟩)) ↔
        0 < loopDepth :=
  Iff.rfl

end StructuralSite

/-- Every structural site reached from the module is locally well formed. -/
structure StructurallyAccepts (module : ParsedModuleV1) : Prop where
  atSite : ∀ {site : StructuralSite},
    StructuralSite.Occurs module site → StructuralSite.Accepts site

/-- Project module acceptance to any reached structural site. -/
theorem StructurallyAccepts.acceptsAt
    {module : ParsedModuleV1} (accepted : StructurallyAccepts module)
    {site : StructuralSite}
    (occurrence : StructuralSite.Occurs module site) :
    StructuralSite.Accepts site :=
  accepted.atSite occurrence

/-- A structurally accepted module admits none of the structural diagnostics. -/
theorem StructurallyAccepts.not_applies
    {module : ParsedModuleV1} (accepted : StructurallyAccepts module)
    {diagnostic : StructuralDiagnostic} :
    ¬StructuralDiagnostic.Applies module diagnostic := by
  intro applies
  cases applies with
  | emptyImportSelection occurrence empty =>
      have site := accepted.acceptsAt occurrence
      unfold StructuralSite.Accepts at site
      rcases site.1 with ⟨entry, member⟩
      simp [empty] at member
  | mixedImportWildcard occurrence mixed least =>
      have site := accepted.acceptsAt occurrence
      unfold StructuralSite.Accepts at site
      exact WildcardListShape.not_mixed_least site.2.1 mixed least
  | duplicateImportSourceName occurrence duplicate =>
      have site := accepted.acceptsAt occurrence
      unfold StructuralSite.Accepts at site
      exact UniqueBy.not_laterDuplicate site.2.2.1 duplicate
  | duplicateImportLocalName occurrence duplicate =>
      have site := accepted.acceptsAt occurrence
      unfold StructuralSite.Accepts at site
      exact UniqueBy.not_laterDuplicate site.2.2.2 duplicate
  | emptyHidingClause occurrence empty =>
      have site := accepted.acceptsAt occurrence
      unfold StructuralSite.Accepts at site
      rcases site.1 with ⟨name, member⟩
      simp [empty] at member
  | duplicateHiddenName occurrence duplicate =>
      have site := accepted.acceptsAt occurrence
      unfold StructuralSite.Accepts at site
      exact UniqueBy.not_laterDuplicate site.2 duplicate
  | emptyLocalExportList occurrence empty =>
      have site := accepted.acceptsAt occurrence
      unfold StructuralSite.Accepts at site
      rcases site.1 with ⟨entry, member⟩
      simp [empty] at member
  | emptyRemoteExportList entries occurrence braced empty =>
      have site := accepted.acceptsAt occurrence
      simp only [StructuralSite.Accepts] at site
      rw [braced] at site
      rcases site.1 with ⟨entry, member⟩
      simp [empty] at member
  | mixedLocalExportWildcard occurrence mixed least =>
      have site := accepted.acceptsAt occurrence
      unfold StructuralSite.Accepts at site
      exact WildcardListShape.not_mixed_least site.2.1 mixed least
  | mixedRemoteExportWildcard occurrence braced mixed least =>
      have site := accepted.acceptsAt occurrence
      simp only [StructuralSite.Accepts] at site
      rw [braced] at site
      exact WildcardListShape.not_mixed_least site.2.1 mixed least
  | duplicateLocalExportName occurrence duplicate =>
      have site := accepted.acceptsAt occurrence
      unfold StructuralSite.Accepts at site
      exact UniqueBy.not_laterDuplicate site.2.2.1 duplicate
  | duplicateRemoteExportName occurrence braced duplicate =>
      have site := accepted.acceptsAt occurrence
      simp only [StructuralSite.Accepts] at site
      rw [braced] at site
      exact UniqueBy.not_laterDuplicate site.2.2 duplicate
  | duplicateExportModuleReference occurrence duplicate =>
      have site := accepted.acceptsAt occurrence
      unfold StructuralSite.Accepts at site
      exact UniqueBy.not_laterDuplicate site.2.2.2 duplicate
  | duplicateExportConstructor occurrence selectionPresent named duplicate =>
      have site := accepted.acceptsAt occurrence
      simp only [StructuralSite.Accepts] at site
      simp only [StructuralSite.ConstructorSelectionAccepts,
        selectionPresent, named] at site
      exact UniqueBy.not_laterDuplicate site duplicate
  | matchPatternArityMismatch occurrence shape armMember mismatch =>
      have site := accepted.acceptsAt occurrence
      simp only [StructuralSite.Accepts] at site
      rw [shape] at site
      unfold StructuralSite.MatchAritiesAgree at site
      exact mismatch (site _ armMember)
  | emptyGenericPragmaTargets occurrence kind empty =>
      have site := accepted.acceptsAt occurrence
      unfold StructuralSite.Accepts at site
      have required := site.1
      unfold StructuralSite.PragmaTargetsPresentWhenRequired at required
      rw [kind] at required
      rcases required with ⟨target, member⟩
      simp [empty] at member
  | duplicatePragmaTarget occurrence duplicate =>
      have site := accepted.acceptsAt occurrence
      unfold StructuralSite.Accepts at site
      exact UniqueBy.not_laterDuplicate site.2 duplicate
  | signatureModifierNotAllowed occurrence selected =>
      have site := accepted.acceptsAt occurrence
      unfold StructuralSite.Accepts at site
      unfold StructuralSite.SignatureModifiersAllowed at site
      cases selected with
      | publicMarker chosen =>
          rw [site.1.1] at chosen
          simp at chosen
      | payableMarker chosen =>
          rw [site.1.2] at chosen
          simp at chosen
  | fallbackModifierNotAllowed occurrence selected =>
      have site := accepted.acceptsAt occurrence
      unfold StructuralSite.Accepts at site
      rw [site.1] at selected
      simp at selected
  | constructorModifierNotAllowed occurrence selected =>
      have site := accepted.acceptsAt occurrence
      unfold StructuralSite.Accepts at site
      rw [site.1] at selected
      simp at selected
  | fallbackHasParameters occurrence nonempty =>
      have site := accepted.acceptsAt occurrence
      unfold StructuralSite.Accepts at site
      exact nonempty site.2.1
  | fallbackHasNonUnitReturn occurrence returnPresent notUnit =>
      have site := accepted.acceptsAt occurrence
      unfold StructuralSite.Accepts at site
      have returnAccepted := site.2.2
      unfold StructuralSite.FallbackReturnAccepts at returnAccepted
      rw [returnPresent] at returnAccepted
      exact notUnit returnAccepted
  | signatureParameterTypeMissing occurrence member missing =>
      have site := accepted.acceptsAt occurrence
      unfold StructuralSite.Accepts at site
      unfold StructuralSite.ParameterTypesPresent at site
      rcases site.2 _ member with ⟨typeExpression, present⟩
      rw [missing] at present
      simp at present
  | constructorParameterTypeMissing occurrence member missing =>
      have site := accepted.acceptsAt occurrence
      unfold StructuralSite.Accepts at site
      unfold StructuralSite.ParameterTypesPresent at site
      rcases site.2 _ member with ⟨typeExpression, present⟩
      rw [missing] at present
      simp at present
  | breakOutsideLoop occurrence shape =>
      have site := accepted.acceptsAt occurrence
      simp only [StructuralSite.Accepts] at site
      rw [shape] at site
      exact Nat.lt_irrefl 0 site
  | continueOutsideLoop occurrence shape =>
      have site := accepted.acceptsAt occurrence
      simp only [StructuralSite.Accepts] at site
      rw [shape] at site
      exact Nat.lt_irrefl 0 site

/-- Absence of every structural diagnostic establishes module acceptance. -/
theorem StructurallyAccepts.of_not_applies
    {module : ParsedModuleV1}
    (noApplies : ∀ diagnostic,
      ¬StructuralDiagnostic.Applies module diagnostic) :
    StructurallyAccepts module := by
  refine ⟨fun {site} occurrence => ?_⟩
  cases site with
  | importSelection selection =>
      simp only [StructuralSite.Accepts]
      constructor
      · apply HasElement.of_ne_nil
        intro empty
        exact noApplies _
          (.emptyImportSelection occurrence empty)
      · constructor
        · apply WildcardListShape.of_no_mixed_least
          intro span mixed least
          exact noApplies _
            (.mixedImportWildcard occurrence mixed least)
        · constructor
          · apply UniqueBy.of_no_laterDuplicate
            intro binding duplicate
            exact noApplies _
              (.duplicateImportSourceName occurrence duplicate)
          · apply UniqueBy.of_no_laterDuplicate
            intro binding duplicate
            exact noApplies _
              (.duplicateImportLocalName occurrence duplicate)
  | hidingClause clause =>
      simp only [StructuralSite.Accepts]
      constructor
      · apply HasElement.of_ne_nil
        intro empty
        exact noApplies _ (.emptyHidingClause occurrence empty)
      · apply UniqueBy.of_no_laterDuplicate
        intro name duplicate
        exact noApplies _ (.duplicateHiddenName occurrence duplicate)
  | localExportList selection =>
      simp only [StructuralSite.Accepts]
      constructor
      · apply HasElement.of_ne_nil
        intro empty
        exact noApplies _ (.emptyLocalExportList occurrence empty)
      · constructor
        · apply WildcardListShape.of_no_mixed_least
          intro span mixed least
          exact noApplies _
            (.mixedLocalExportWildcard occurrence mixed least)
        · constructor
          · apply UniqueBy.of_no_laterDuplicate
            intro item duplicate
            exact noApplies _
              (.duplicateLocalExportName occurrence duplicate)
          · apply UniqueBy.of_no_laterDuplicate
            intro reference duplicate
            exact noApplies _
              (.duplicateExportModuleReference occurrence duplicate)
  | remoteExportSelection selection =>
      simp only [StructuralSite.Accepts]
      cases payloadEq : selection.payload with
      | dotWildcard marker => exact True.intro
      | braced entries =>
          constructor
          · apply HasElement.of_ne_nil
            intro empty
            exact noApplies _
              (.emptyRemoteExportList entries occurrence payloadEq empty)
          · constructor
            · apply WildcardListShape.of_no_mixed_least
              intro span mixed least
              exact noApplies _
                (.mixedRemoteExportWildcard occurrence payloadEq mixed least)
            · apply UniqueBy.of_no_laterDuplicate
              intro item duplicate
              exact noApplies _
                (.duplicateRemoteExportName occurrence payloadEq duplicate)
  | exportItem item =>
      simp only [StructuralSite.Accepts]
      cases selectionPresent : item.payload.constructors with
      | none =>
          exact True.intro
      | some selection =>
          cases selectionShape : selection.payload with
          | all marker =>
              simp only [StructuralSite.ConstructorSelectionAccepts,
                selectionShape]
          | named constructors =>
              simp only [StructuralSite.ConstructorSelectionAccepts,
                selectionShape]
              apply UniqueBy.of_no_laterDuplicate
              intro name duplicate
              exact noApplies _ (.duplicateExportConstructor occurrence
                selectionPresent selectionShape duplicate)
  | pragma declaration =>
      simp only [StructuralSite.Accepts]
      constructor
      · unfold StructuralSite.PragmaTargetsPresentWhenRequired
        cases kindEq : declaration.payload.kind.payload with
        | noCoverageCondition => exact True.intro
        | noPattersonCondition => exact True.intro
        | noBoundedVariableCondition => exact True.intro
        | noGenericInstanceFor =>
            apply HasElement.of_ne_nil
            intro empty
            exact noApplies _
              (.emptyGenericPragmaTargets occurrence kindEq empty)
      · apply UniqueBy.of_no_laterDuplicate
        intro target duplicate
        exact noApplies _ (.duplicatePragmaTarget occurrence duplicate)
  | signature modifierContext parameterContext functionSignature =>
      simp only [StructuralSite.Accepts]
      constructor
      · unfold StructuralSite.SignatureModifiersAllowed
        cases modifierContext with
        | none => exact True.intro
        | some context =>
            constructor
            · cases publicEq : functionSignature.payload.public with
              | none => exact rfl
              | some marker =>
                  exact False.elim (noApplies _
                    (.signatureModifierNotAllowed occurrence
                      (.publicMarker publicEq)))
            · cases payableEq : functionSignature.payload.payable with
              | none => exact rfl
              | some marker =>
                  exact False.elim (noApplies _
                    (.signatureModifierNotAllowed occurrence
                      (.payableMarker payableEq)))
      · unfold StructuralSite.ParameterTypesPresent
        intro parameter member
        cases typeEq : parameter.payload.type with
        | none =>
            exact False.elim (noApplies _
              (.signatureParameterTypeMissing occurrence member typeEq))
        | some typeExpression => exact ⟨typeExpression, rfl⟩
  | fallback declaration =>
      simp only [StructuralSite.Accepts]
      constructor
      · cases publicEq : declaration.payload.public with
        | none => exact rfl
        | some marker =>
            exact False.elim (noApplies _
              (.fallbackModifierNotAllowed occurrence publicEq))
      · constructor
        · by_cases empty : declaration.payload.parameters = []
          · exact empty
          · exact False.elim (noApplies _
              (.fallbackHasParameters occurrence empty))
        · cases returnEq : declaration.payload.returnType with
          | none => exact True.intro
          | some returnType =>
              by_cases grouped : GroupedUnit returnType
              · exact grouped
              · exact False.elim (noApplies _
                  (.fallbackHasNonUnitReturn occurrence returnEq grouped))
  | contractConstructor declaration =>
      simp only [StructuralSite.Accepts]
      constructor
      · cases publicEq : declaration.payload.public with
        | none => exact rfl
        | some marker =>
            exact False.elim (noApplies _
              (.constructorModifierNotAllowed occurrence publicEq))
      · unfold StructuralSite.ParameterTypesPresent
        intro parameter member
        cases typeEq : parameter.payload.type with
        | none =>
            exact False.elim (noApplies _
              (.constructorParameterTypeMissing occurrence member typeEq))
        | some typeExpression => exact ⟨typeExpression, rfl⟩
  | statement loopDepth statementNode =>
      simp only [StructuralSite.Accepts]
      cases payloadEq : statementNode.payload with
      | assignment operator left right => exact True.intro
      | letBinding binding => exact True.intro
      | block body => exact True.intro
      | expression expressionNode terminator => exact True.intro
      | «return» value terminator => exact True.intro
      | «match» scrutinees arms terminator =>
          unfold StructuralSite.MatchAritiesAgree
          intro arm member
          by_cases arityEq : arm.payload.patterns.toList.length =
              scrutinees.toList.length
          · exact arityEq
          · exact False.elim (noApplies _
              (.matchPatternArityMismatch occurrence payloadEq member arityEq))
      | assembly slice => exact True.intro
      | ifThenElse condition thenBody elseBody => exact True.intro
      | forLoop initializers condition post body => exact True.intro
      | «break» terminator =>
          cases loopDepth with
          | zero =>
              exact False.elim (noApplies _
                (.breakOutsideLoop occurrence payloadEq))
          | succ depth => exact Nat.zero_lt_succ depth
      | «continue» terminator =>
          cases loopDepth with
          | zero =>
              exact False.elim (noApplies _
                (.continueOutsideLoop occurrence payloadEq))
          | succ depth => exact Nat.zero_lt_succ depth
  | expression expressionNode =>
      exact StructuralSite.accepts_expression expressionNode
  | pattern patternNode =>
      exact StructuralSite.accepts_pattern patternNode
  | body loopDepth bodyNode =>
      exact StructuralSite.accepts_body loopDepth bodyNode
  | forInit item => exact StructuralSite.accepts_forInit item
  | forPost item => exact StructuralSite.accepts_forPost item

/-- Positive structural acceptance is exactly absence of applicable diagnostics. -/
@[simp] theorem structurallyAccepts_iff_no_applies
    (module : ParsedModuleV1) :
    StructurallyAccepts module ↔
      ∀ diagnostic, ¬StructuralDiagnostic.Applies module diagnostic := by
  constructor
  · intro accepted diagnostic
    exact accepted.not_applies
  · exact StructurallyAccepts.of_not_applies

end Solcore.Surface.Multi
