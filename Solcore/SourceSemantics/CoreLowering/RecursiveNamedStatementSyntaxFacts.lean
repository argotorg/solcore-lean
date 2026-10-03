import Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchTree

/-! Static annotation and continuation facts from the independent source
judgments. A returned annotation uses the actual control return type. Universal
stopping keeps an actual return/default/branch/prefix receipt; BodyCompletes is
never used to manufacture that receipt. Exhaustive no-default stopping remains
at its existing typed pointwise boundary. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedStatementSyntaxFacts
open Frontend SourceInference
open ReachableStatementContinuations

/-- The legacy returned annotation follows the actual source typing derivation,
including ordered match facts and lexical context changes. -/
theorem returned_type {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {statements : List StatementId} {facts : BodyFacts}
    (typed : StatementsHaveType source control context statements final facts)
    (returns : facts.sawReturn = true) : facts.type = control.returnType := by
  have result : facts.sawReturn = true → facts.type = control.returnType := by
    apply StatementsHaveType.rec (source := source) (t := typed)
      (motive_1 := fun _ _ _ _ => True)
      (motive_2 := fun _ _ _ _ _ => True)
      (motive_3 := fun _ _ _ _ => True)
      (motive_4 := fun _ _ _ _ _ => True)
      (motive_5 := fun _ _ _ _ => True)
      (motive_6 := fun _ _ _ _ _ => True)
      (motive_7 := fun _ _ _ => True)
      (motive_8 := fun control _ _ _ facts _ => facts.sawReturn = true → facts.type = control.returnType)
      (motive_9 := fun control _ _ _ facts _ => facts.sawReturn = true → facts.type = control.returnType)
      (motive_10 := fun _ _ _ _ _ => True)
      (motive_11 := fun _ _ _ _ _ => True)
      (motive_12 := fun control _ _ _ facts _ => facts.sawReturn = true → facts.type = control.returnType)
      (motive_13 := fun control _ _ _ facts _ => ∀ fact ∈ facts, fact.sawReturn = true → fact.type = control.returnType)
    all_goals try { intros; exact True.intro }
    all_goals try { intros; simp_all }
    case singleton =>
      intro control context final id facts head ih returns
      have r : facts.sawReturn = true := returns
      simpa [BodyFacts.singleton, r] using ih r
    case cons =>
      intro control context middle final id next rest headFacts tailFacts head tail headIH tailIH returns
      cases h : tailFacts.sawReturn with
      | true => simpa [BodyFacts.cons, h] using tailIH h
      | false =>
        have r : headFacts.sawReturn = true := by simpa [BodyFacts.cons, h] using returns
        simpa [BodyFacts.cons, h, r] using headIH r
    case nil => simp [BodyFacts.empty]
    case cons =>
      intro control context type arm arms fact facts head tail headIH tailIH candidate member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact headIH
      · exact tailIH candidate member
  exact result returns

/-- Prefixing a statically typed ordinary-or-terminal head preserves the actual
stopping selection in the tail. It does not require the head to fall through. -/
theorem prefix_stopped {source : TypedSource} {control : ControlContext}
    {context next : SourceSemantics.Context} {id : StatementId} {node : StatementNode}
    {facts : StatementFacts} {rest : List StatementId} {summary : ControlSummary}
    (found : source.lookupStatement? id = some node)
    (head : StatementHasType source control context id next facts)
    (tail : StoppingStatements source rest summary) :
    StoppingStatements source (id :: rest) (facts.control.sequence summary) :=
  .prefix found head tail

private theorem same_form {source : TypedSource} {id : StatementId} {node other : StatementNode}
    (first : source.lookupStatement? id = some node)
    (second : source.lookupStatement? id = some other) : other.form = node.form := by
  cases Option.some.inj (second.symm.trans first)
  rfl

/-- Only the actual block stopping constructor can match this source form. -/
theorem stopped_block {source : TypedSource} {id : StatementId} {node : StatementNode}
    {body : List StatementId} {summary : ControlSummary}
    (found : source.lookupStatement? id = some node) (form : node.form = .block body)
    (stopped : StoppingStatement source id summary) :
    ∃ inner, StoppingStatements source body inner := by
  cases stopped <;> have eq := same_form found (by assumption) <;> simp_all
  exact ⟨_, by assumption⟩

/-- Universal conditional stopping retains both actual branch selections. -/
theorem stopped_if {source : TypedSource} {id : StatementId} {node : StatementNode}
    {condition : ExpressionId} {left right : List StatementId} {summary : ControlSummary}
    (found : source.lookupStatement? id = some node) (form : node.form = .ifThen condition left (some right))
    (stopped : StoppingStatement source id summary) :
    (∃ l, StoppingStatements source left l) ∧ (∃ r, StoppingStatements source right r) := by
  cases stopped <;> have eq := same_form found (by assumption) <;> simp_all
  exact ⟨⟨_, by assumption⟩, ⟨_, by assumption⟩⟩

/-- Static arm facts retain the compiler's full ordered case count. -/
theorem cases_length {source : TypedSource} {control : ControlContext} {context : SourceSemantics.Context}
    {type : TypeSystem.Ty} {cases : List TypedMatchCase} {facts : List BodyFacts}
    (typed : MatchCasesHaveType source control context type cases facts) : cases.length = facts.length := by
  apply MatchCasesHaveType.rec (source := source) (t := typed)
    (motive_1 := fun _ _ _ _ => True)
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ => True)
    (motive_6 := fun _ _ _ _ _ => True)
    (motive_7 := fun _ _ _ => True)
    (motive_8 := fun _ _ _ _ _ _ => True)
    (motive_9 := fun _ _ _ _ _ _ => True)
    (motive_10 := fun _ _ _ _ _ => True)
    (motive_11 := fun _ _ _ _ _ => True)
    (motive_12 := fun _ _ _ _ _ _ => True)
    (motive_13 := fun _ _ _ cases facts _ => cases.length = facts.length)
  all_goals intros; first | exact True.intro | simp_all

private theorem zip_fact {cases : List TypedMatchCase} {facts : List BodyFacts} {arm : TypedMatchCase}
    (length : cases.length = facts.length) (member : arm ∈ cases) :
    ∃ fact, (arm, fact) ∈ cases.zip facts := by
  induction cases generalizing facts with
  | nil => cases member
  | cons head tail ih =>
    cases facts with
    | nil => simp at length
    | cons fact rest =>
      have sizes : tail.length = rest.length := Nat.succ.inj length
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨fact, List.mem_cons_self⟩
      · obtain ⟨chosen, present⟩ := ih sizes member
        exact ⟨chosen, List.mem_cons_of_mem _ present⟩

/-- A stopping match view comes only from the actual present-default receipt.
No no-default exhaustiveness certificate is cast to this universal boundary. -/
theorem stopped_match {source : TypedSource} {id : StatementId} {node : StatementNode}
    {resolution : MatchResolution} {summary : ControlSummary}
    (found : source.lookupStatement? id = some node) (form : node.form = .matchWith resolution)
    (stopped : StoppingStatement source id summary) :
    ReachableMatchContinuations.DefaultStopped source id resolution := by
  cases stopped <;> have eq := same_form found (by assumption) <;> simp_all
  case matchDefault =>
    subst_vars
    rename_i actualNode resolution fallback control context type facts defaultFinal defaultFacts summary present casesTyped defaultTyped merged arms defaultStops originalFound
    refine ReachableMatchContinuations.DefaultStopped.of_source originalFound form present ⟨?_, ?_⟩
    · intro arm member
      have length := cases_length casesTyped
      obtain ⟨fact, zipped⟩ := zip_fact length member
      exact GenericLexicalStatements.Stopped.of_source (arms arm fact zipped)
    · intro body same
      cases Option.some.inj (present.symm.trans same)
      exact GenericLexicalStatements.Stopped.of_source defaultStops

private theorem sequence_stopped {head tail : ControlSummary} (stops : head.fallthrough = none) :
    head.sequence tail = head := by
  cases head
  simp_all [ControlSummary.sequence, ControlSummary.canFallthrough]

/-- Static input for one binding actually retained in a source body/header. -/
def BinderReceipt (source : TypedSource) (binder : TypedBinder) : Prop :=
  SourceCoreDataPlaces.rootBinder source binder.id = .ok binder ∧ binder.scheme.quantified = [] ∧
    source.inputs.any (fun input => decide (input.id = binder.id)) = false

/-- The actual finite assignment children and source root correspondence.
These are source typing/admission receipts, with no runtime law. -/
structure AssignmentReceipt (source : TypedSource) (expressionSyntax : ExpressionId → Prop)
    (context : SourceSemantics.Context) (assignment : AssignmentResolution)
    (operator : Syntax.ValueAssignOp) (rhs : ExpressionId) : Prop where
  projections : ∀ binder, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder →
    SourceProjectionsHaveType source context binder.scheme.body assignment.target.projections assignment.target.type
  writable : ∀ binder, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder →
    WritableLocal context assignment.target.root binder.scheme.body
  right : ExpressionHasType source context rhs assignment.target.type
  profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
    SourceCoreRawMetadata.runtimeType assignment.target.type = .integer
  children : ∀ id, id ∈ rhs :: DataPlaceKeyOrder.sourceKeys assignment.target.projections →
    expressionSyntax id ∧ ∃ node, source.lookupExpression? id = some node ∧ ExpressionHasType source context id node.type

structure UnaryReceipt (source : TypedSource) (context : SourceSemantics.Context)
    (assignment : AssignmentResolution) : Prop where
  writable : ∀ binder, SourceCoreDataPlaces.rootBinder source assignment.target.root = .ok binder →
    WritableLocal context assignment.target.root binder.scheme.body
  bare : assignment.target.projections = []
  profile : SourceCoreRawMetadata.runtimeType assignment.target.type = .word ∨
    SourceCoreRawMetadata.runtimeType assignment.target.type = .integer

/- Support is indexed by the original independent typing proof, rather than a
new source grammar. Its Bool index records availability of a universal stopping
receipt. No-default cases retain false; an actual later stopper can still make
the complete sequence true. Only the static children actually present in the
typing derivation occur here. -/
mutual
  inductive StatementReceipts (source : TypedSource) (expressionSyntax : ExpressionId → Prop) :
      {control : ControlContext} → {context : SourceSemantics.Context} → {id : StatementId} →
      {final : SourceSemantics.Context} → {facts : StatementFacts} →
      StatementHasType source control context id final facts → Bool → Prop where
    | letUninitialized {control context final id node binder contains form mono generalizes extension annotation}
        (binderReceipt : BinderReceipt source binder) :
        StatementReceipts source expressionSyntax
          (@StatementHasType.letUninitialized source control context final id node binder contains form mono generalizes extension annotation) false
    | letInitialized {control context final id node binder initializer contains form initial mono generalizes extension annotation}
        (binderReceipt : BinderReceipt source binder) (value : expressionSyntax initializer) :
        StatementReceipts source expressionSyntax
          (@StatementHasType.letInitialized source control context final id node binder initializer contains form initial mono generalizes extension annotation) false
    | returnUnit {control context id node contains form unit annotation} :
        StatementReceipts source expressionSyntax
          (@StatementHasType.returnUnit source control context id node contains form unit annotation) true
    | returnValue {control context id node value contains form typed annotation}
        (expression : expressionSyntax value) :
        StatementReceipts source expressionSyntax
          (@StatementHasType.returnValue source control context id node value contains form typed annotation) true
    | expressionValue {control context id node expression type contains form typed annotation}
        (value : expressionSyntax expression) :
        StatementReceipts source expressionSyntax
          (@StatementHasType.expressionValue source control context id node expression type contains form typed annotation) false
    | expressionDiscard {control context id node expression type contains form typed annotation}
        (value : expressionSyntax expression) :
        StatementReceipts source expressionSyntax
          (@StatementHasType.expressionDiscard source control context id node expression type contains form typed annotation) false
    | assignValue {control context id node assignment operator rhs contains form typed annotation}
        (receipt : AssignmentReceipt source expressionSyntax context assignment operator rhs) :
        StatementReceipts source expressionSyntax
          (@StatementHasType.assignValue source control context id node assignment operator rhs contains form typed annotation) false
    | assignBitNot {control context id node assignment contains form typed annotation}
        (receipt : UnaryReceipt source context assignment) :
        StatementReceipts source expressionSyntax
          (@StatementHasType.assignBitNot source control context id node assignment contains form typed annotation) false
    | ifWithoutElse {control context thenFinal id node condition body facts contains form conditionTyped bodyTyped annotation ready}
        (conditionSyntax : expressionSyntax condition)
        (bodyReceipt : BodyReceipts source expressionSyntax bodyTyped ready) :
        StatementReceipts source expressionSyntax
          (@StatementHasType.ifWithoutElse source control context thenFinal id node condition body facts contains form conditionTyped bodyTyped annotation) false
    | ifWithElse {control context leftFinal rightFinal id node condition left right leftFacts rightFacts
        contains form conditionTyped leftTyped rightTyped annotation leftReady rightReady}
        (conditionSyntax : expressionSyntax condition)
        (leftReceipt : BodyReceipts source expressionSyntax leftTyped leftReady)
        (rightReceipt : BodyReceipts source expressionSyntax rightTyped rightReady)
        (admitted : control.returnType = .unit ∨ (leftFacts.sawReturn && rightFacts.sawReturn) = false ∨
          (leftReady = true ∧ rightReady = true)) :
        StatementReceipts source expressionSyntax
          (@StatementHasType.ifWithElse source control context leftFinal rightFinal id node condition left right leftFacts rightFacts
            contains form conditionTyped leftTyped rightTyped annotation) (leftReady && rightReady)
    | block {control context innerFinal id node statements facts contains form typed annotation ready}
        (inner : BodyReceipts source expressionSyntax typed ready) :
        StatementReceipts source expressionSyntax
          (@StatementHasType.block source control context innerFinal id node statements facts contains form typed annotation) ready
    | matchWithoutDefault {control context id node resolution type facts summary
        contains form absent scrutineeTyped casesTyped requirements exhaustive merged annotation ready}
        (scrutinee : expressionSyntax resolution.scrutinee)
        (cases : CasesReceipts source expressionSyntax casesTyped ready)
        (hidden : source.inputs.any (fun input => decide (input.id = resolution.hiddenScrutinee)) = false)
        (ordinary : ∀ arm ∈ resolution.cases, ∀ binder ∈ arm.pattern.binderIds,
          source.inputs.any (fun input => decide (input.id = binder)) = false) :
        StatementReceipts source expressionSyntax
          (@StatementHasType.matchWithoutDefault source control context id node resolution type facts summary
            contains form absent scrutineeTyped casesTyped requirements exhaustive merged annotation) false
    | matchWithDefault {control context defaultFinal id node resolution fallback type facts defaultFacts summary
        contains form present scrutineeTyped casesTyped defaultTyped requirements merged annotation ready defaultReady}
        (scrutinee : expressionSyntax resolution.scrutinee)
        (cases : CasesReceipts source expressionSyntax casesTyped ready)
        (fallbackReceipt : BodyReceipts source expressionSyntax defaultTyped defaultReady)
        (hidden : source.inputs.any (fun input => decide (input.id = resolution.hiddenScrutinee)) = false)
        (ordinary : ∀ arm ∈ resolution.cases, ∀ binder ∈ arm.pattern.binderIds,
          source.inputs.any (fun input => decide (input.id = binder)) = false) :
        StatementReceipts source expressionSyntax
          (@StatementHasType.matchWithDefault source control context defaultFinal id node resolution fallback type facts defaultFacts summary
            contains form present scrutineeTyped casesTyped defaultTyped requirements merged annotation) (ready && defaultReady)
    | forLoop {control context loopContext postContext bodyFinal id node initializer condition post statements facts
        contains form initializerTyped conditionTyped bodyTyped postTyped annotation ready}
        (initial : ItemsReceipts source expressionSyntax initializerTyped)
        (conditionSyntax : expressionSyntax condition)
        (bodyReceipt : BodyReceipts source expressionSyntax bodyTyped ready)
        (postReceipt : ItemsReceipts source expressionSyntax postTyped) :
        StatementReceipts source expressionSyntax
          (@StatementHasType.forLoop source control context loopContext postContext bodyFinal id node initializer post condition statements facts
            contains form initializerTyped conditionTyped bodyTyped postTyped annotation) false
    | whileLoop {control context final id node condition statements facts contains form conditionTyped bodyTyped annotation ready}
        (conditionSyntax : expressionSyntax condition)
        (bodyReceipt : BodyReceipts source expressionSyntax bodyTyped ready) :
        StatementReceipts source expressionSyntax
          (@StatementHasType.whileLoop source control context final id node condition statements facts
            contains form conditionTyped bodyTyped annotation) false
    | breakStmt {control context id node contains form allowed annotation} :
        StatementReceipts source expressionSyntax
          (@StatementHasType.breakStmt source control context id node contains form allowed annotation) true
    | continueStmt {control context id node contains form allowed annotation} :
        StatementReceipts source expressionSyntax
          (@StatementHasType.continueStmt source control context id node contains form allowed annotation) true

  inductive BodyReceipts (source : TypedSource) (expressionSyntax : ExpressionId → Prop) :
      {control : ControlContext} → {context : SourceSemantics.Context} → {statements : List StatementId} →
      {final : SourceSemantics.Context} → {facts : BodyFacts} →
      StatementsHaveType source control context statements final facts → Bool → Prop where
    | nil (control context) : BodyReceipts source expressionSyntax (StatementsHaveType.nil control context) false
    | singleton {control context final id facts head ready}
        (headReceipt : StatementReceipts source expressionSyntax head ready)
        (admitted : (BodyFacts.singleton facts).type = control.returnType →
          control.returnType = .unit ∨ facts.sawReturn = false ∨ ready = true) :
        BodyReceipts source expressionSyntax (@StatementsHaveType.singleton source control context final id facts head) ready
    | cons {control context middle final id next rest headFacts tailFacts head tail headReady tailReady}
        (headReceipt : StatementReceipts source expressionSyntax head headReady)
        (tailReceipt : BodyReceipts source expressionSyntax tail tailReady)
        (admitted : (BodyFacts.cons headFacts tailFacts).type = control.returnType →
          tailFacts.type = control.returnType ∨ (headFacts.sawReturn = true ∧ headReady = true)) :
        BodyReceipts source expressionSyntax
          (@StatementsHaveType.cons source control context middle final id next rest headFacts tailFacts head tail) (headReady || tailReady)

  inductive ItemReceipts (source : TypedSource) (expressionSyntax : ExpressionId → Prop) :
      {control : ControlContext} → {context : SourceSemantics.Context} → {item : ForItemForm} →
      {final : SourceSemantics.Context} → ForItemHasType source control context item final → Prop where
    | letUninitialized {control context final binder mono generalizes extension}
        (receipt : BinderReceipt source binder) : ItemReceipts source expressionSyntax
          (@ForItemHasType.letUninitialized source control context final binder mono generalizes extension)
    | letInitialized {control context final binder expression typed mono generalizes extension}
        (receipt : BinderReceipt source binder) (value : expressionSyntax expression) : ItemReceipts source expressionSyntax
          (@ForItemHasType.letInitialized source control context final binder expression typed mono generalizes extension)
    | expression {control context expression type typed} (value : expressionSyntax expression) :
        ItemReceipts source expressionSyntax (@ForItemHasType.expression source control context expression type typed)
    | assignValue {control context assignment operator expression typed}
        (receipt : AssignmentReceipt source expressionSyntax context assignment operator expression) :
        ItemReceipts source expressionSyntax (@ForItemHasType.assignValue source control context assignment operator expression typed)
    | assignBitNot {control context assignment typed} (receipt : UnaryReceipt source context assignment) :
        ItemReceipts source expressionSyntax (@ForItemHasType.assignBitNot source control context assignment typed)

  inductive ItemsReceipts (source : TypedSource) (expressionSyntax : ExpressionId → Prop) :
      {control : ControlContext} → {context : SourceSemantics.Context} → {items : List ForItemForm} →
      {final : SourceSemantics.Context} → ForItemsHaveType source control context items final → Prop where
    | nil (control context) : ItemsReceipts source expressionSyntax (ForItemsHaveType.nil control context)
    | cons {control context middle final item items head tail}
        (headReceipt : ItemReceipts source expressionSyntax head)
        (tailReceipt : ItemsReceipts source expressionSyntax tail) : ItemsReceipts source expressionSyntax
          (@ForItemsHaveType.cons source control context middle final item items head tail)

  inductive CaseReceipts (source : TypedSource) (expressionSyntax : ExpressionId → Prop) :
      {control : ControlContext} → {context : SourceSemantics.Context} → {type : TypeSystem.Ty} →
      {arm : TypedMatchCase} → {facts : BodyFacts} →
      MatchCaseHasType source control context type arm facts → Bool → Prop where
    | intro {control context type arm binders arity armContext final facts pattern extended typed ready}
        (body : BodyReceipts source expressionSyntax typed ready) : CaseReceipts source expressionSyntax
          (@MatchCaseHasType.intro source control context type arm binders arity armContext final facts pattern extended typed) ready

  inductive CasesReceipts (source : TypedSource) (expressionSyntax : ExpressionId → Prop) :
      {control : ControlContext} → {context : SourceSemantics.Context} → {type : TypeSystem.Ty} →
      {arms : List TypedMatchCase} → {facts : List BodyFacts} →
      MatchCasesHaveType source control context type arms facts → Bool → Prop where
    | nil (control context type) : CasesReceipts source expressionSyntax (MatchCasesHaveType.nil control context type) true
    | cons {control context type arm arms fact facts head tail headReady tailReady}
        (headReceipt : CaseReceipts source expressionSyntax head headReady)
        (tailReceipt : CasesReceipts source expressionSyntax tail tailReady) : CasesReceipts source expressionSyntax
          (@MatchCasesHaveType.cons source control context type arm arms fact facts head tail) (headReady && tailReady)
end

/-- Universal stopping is constructed from the selected default/return/block/
if and typed prefix support, at the original typing contexts and source. -/
theorem BodyReceipts.stopping {source : TypedSource} {expressionSyntax : ExpressionId → Prop}
    {control : ControlContext} {context final : SourceSemantics.Context}
    {statements : List StatementId} {facts : BodyFacts} {typed : StatementsHaveType source control context statements final facts}
    {ready : Bool} (unique : NodeOccurrencesUnique source)
    (receipt : BodyReceipts source expressionSyntax typed ready) (available : ready = true) :
    StoppingStatements source statements facts.control := by
  have result : ready = true → StoppingStatements source statements facts.control := by
    apply BodyReceipts.rec (t := receipt)
      (motive_1 := fun {control context id final facts} _ ready _ => ready = true → StoppingStatement source id facts.control)
      (motive_2 := fun {control context ids final facts} _ ready _ => ready = true → StoppingStatements source ids facts.control)
      (motive_3 := fun {control context item final} _ _ => True)
      (motive_4 := fun {control context items final} _ _ => True)
      (motive_5 := fun {control context type arm facts} _ ready _ => ready = true → StoppingStatements source arm.body facts.control)
      (motive_6 := fun {control context type arms facts} _ ready _ => ready = true → ∀ arm fact,
        (arm, fact) ∈ arms.zip facts → StoppingStatements source arm.body fact.control)
    all_goals try { intros; exact True.intro }
    all_goals try { intros; contradiction }
    case returnUnit => intros; exact .returnUnit (lookupStatement?_complete unique (by assumption)) (by assumption)
    case returnValue => intros; exact .returnValue (lookupStatement?_complete unique (by assumption)) (by assumption)
    case breakStmt => intros; exact .breaking (lookupStatement?_complete unique (by assumption)) (by assumption)
    case continueStmt => intros; exact .continuing (lookupStatement?_complete unique (by assumption)) (by assumption)
    case ifWithElse =>
      intros
      rename_i leftIH rightIH available
      rcases Bool.and_eq_true_iff.mp available with ⟨leftReady, rightReady⟩
      exact .conditional (lookupStatement?_complete unique (by assumption)) (by assumption) (leftIH leftReady) (rightIH rightReady)
    case block =>
      intros
      rename_i bodyIH available
      exact .block (lookupStatement?_complete unique (by assumption)) (by assumption) (bodyIH available)
    case matchWithDefault =>
      intros
      rename_i casesIH defaultIH available
      rcases Bool.and_eq_true_iff.mp available with ⟨caseReady, defaultReady⟩
      exact .matchDefault (lookupStatement?_complete unique (by assumption)) (by assumption) (by assumption)
        (by assumption) (by assumption) (by assumption) (casesIH caseReady) (defaultIH defaultReady)
    case singleton =>
      intros
      rename_i headIH available
      exact .stop (headIH available)
    case cons =>
      intros
      rename_i actualControl initial middle final id next rest headFacts tailFacts headTyped tailTyped headReady tailReady headReceipt tailReceipt admitted headIH tailIH available
      rcases Bool.or_eq_true_iff.mp available with headReady | tailReady
      · have head := headIH headReady
        change StoppingStatements source (id :: next :: rest) (headFacts.control.sequence tailFacts.control)
        rw [sequence_stopped head.no_fallthrough]
        exact .stop head
      · obtain ⟨node, present, _⟩ := Dynamic.StatementHasType.controlFormTyping headTyped
        exact .prefix (lookupStatement?_complete unique present) headTyped (tailIH tailReady)
    case intro =>
      intros
      rename_i bodyIH available
      exact bodyIH available
    case cons =>
      intros
      rename_i headIH tailIH available arm fact member
      rcases Bool.and_eq_true_iff.mp available with ⟨headReady, tailReady⟩
      rcases List.mem_cons.mp member with same | member
      · cases same
        exact headIH headReady
      · exact tailIH tailReady arm fact member
  exact result available

private theorem singleton_stopping {source : TypedSource} {id : StatementId} {summary : ControlSummary}
    (stops : StoppingStatements source [id] summary) : StoppingStatement source id summary := by
  cases stops with
  | stop head => exact head
  | «prefix» _ _ tail => exact False.elim (tail.nonempty rfl)

/-- The statement receipt uses the same universal stopping proof as its
one-statement body; no completion-to-stopping implication is assumed. -/
theorem StatementReceipts.stopping {source : TypedSource} {expressionSyntax : ExpressionId → Prop}
    {control : ControlContext} {context final : SourceSemantics.Context}
    {id : StatementId} {facts : StatementFacts} {typed : StatementHasType source control context id final facts}
    {ready : Bool} (unique : NodeOccurrencesUnique source)
    (receipt : StatementReceipts source expressionSyntax typed ready) (available : ready = true) :
    StoppingStatement source id facts.control := by
  have body : BodyReceipts source expressionSyntax (StatementsHaveType.singleton typed) ready :=
    .singleton receipt (fun _ => .inr (.inr available))
  exact singleton_stopping (body.stopping unique available)

/-- A fixed ordered source binder extension fixes the complete lexical context. -/
theorem binders_context_eq {owner : Resolved.DeclarationId} {context left right : SourceSemantics.Context}
    {binders : List TypedBinder} (one : BindersExtend owner context binders left)
    (two : BindersExtend owner context binders right) : left = right := by
  induction one generalizing right with
  | nil => cases two; rfl
  | cons first rest ih =>
    cases two with
    | cons other tail =>
      cases first
      cases other
      exact ih tail

/-- Typed pattern binders retain their full source order before context transport. -/
theorem pattern_context_eq {source : TypedSource} {context left right : SourceSemantics.Context}
    {pattern : TypedMatchPattern} {type : TypeSystem.Ty} {one two : List TypedBinder} {a b : Nat}
    (first : TypedMatchPatternHasType context pattern type one a)
    (second : TypedMatchPatternHasType context pattern type two b)
    (leftExtension : BindersExtend source.owner context one left)
    (rightExtension : BindersExtend source.owner context two right) : left = right := by
  have same : one = two := (CompatiblePatternSourceBinders.pattern_binders first).symm.trans
    (CompatiblePatternSourceBinders.pattern_binders second)
  subst two
  exact binders_context_eq leftExtension rightExtension

/-- Every ordered typed case keeps its own actual body stopping receipt. -/
theorem CasesReceipts.stopping {source : TypedSource} {expressionSyntax : ExpressionId → Prop}
    {control : ControlContext} {context : SourceSemantics.Context} {type : TypeSystem.Ty}
    {arms : List TypedMatchCase} {facts : List BodyFacts}
    {typed : MatchCasesHaveType source control context type arms facts} {ready : Bool}
    (unique : NodeOccurrencesUnique source) (receipt : CasesReceipts source expressionSyntax typed ready)
    (available : ready = true) :
    ∀ arm fact, (arm, fact) ∈ arms.zip facts → StoppingStatements source arm.body fact.control := by
  cases receipt with
  | nil => intro arm fact member; cases member
  | @cons _ _ _ arm arms fact facts head tail headReady tailReady first rest =>
    rcases Bool.and_eq_true_iff.mp available with ⟨headAvailable, tailAvailable⟩
    intro selected selectedFacts member
    rcases List.mem_cons.mp member with same | member
    · cases same
      cases first with
      | intro body => exact body.stopping unique headAvailable
    · exact rest.stopping unique tailAvailable selected selectedFacts member
termination_by arms.length

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedStatementSyntaxFacts
