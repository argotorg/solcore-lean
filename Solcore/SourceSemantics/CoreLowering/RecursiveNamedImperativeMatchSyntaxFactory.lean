import Solcore.SourceSemantics.CoreLowering.RecursiveNamedStatementSyntaxFacts
import Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchCertificates

/-! The syntax factory consumes independent source typing and its actual finite
static children. It calls the existing extraction traversal once. Universal
stopping is limited to retained returns, branches and present defaults;
no-default-only stopping remains at the typed pointwise boundary. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeMatchSyntaxFactory
open Frontend SourceInference RecursiveNamedStatementSyntaxFacts

private abbrev BodySyntax (source : TypedSource) (expressionSyntax : ExpressionId → Prop)
    (context : SourceSemantics.Context) (mode : Bool) (ids : List StatementId) (expected : TypeSystem.Ty) :=
  GenericImperativeMatch.Syntax source expressionSyntax context (.statements mode ids) expected

private structure StatementSyntax (source : TypedSource) (expressionSyntax : ExpressionId → Prop)
    (control : ControlContext) (context : SourceSemantics.Context) (id : StatementId)
    (final : SourceSemantics.Context) (facts : StatementFacts) (ready : Bool) : Prop where
  prepend : ∀ mode rest, (mode = false ∨ rest ≠ [] ∨ facts.hasValue = false ∨ facts.sawReturn = true) →
    BodySyntax source expressionSyntax final mode rest control.returnType →
    BodySyntax source expressionSyntax context mode (id :: rest) control.returnType
  finish : facts.sawReturn = true → ready = true → ∀ mode rest,
    BodySyntax source expressionSyntax context mode (id :: rest) control.returnType
  value : facts.sawReturn = false → facts.hasValue = true → facts.type = control.returnType →
    BodySyntax source expressionSyntax context true [id] control.returnType

private theorem StatementSyntax.singleton {source : TypedSource} {expressionSyntax : ExpressionId → Prop}
    {control : ControlContext} {context final : SourceSemantics.Context} {id : StatementId}
    {facts : StatementFacts} {ready : Bool}
    (result : StatementSyntax source expressionSyntax control context id final facts ready)
    (same : (BodyFacts.singleton facts).type = control.returnType)
    (admitted : control.returnType = .unit ∨ facts.sawReturn = false ∨ ready = true) :
    BodySyntax source expressionSyntax context true [id] control.returnType := by
  cases returned : facts.sawReturn with
  | true =>
    rcases admitted with unit | noReturn | stops
    · exact result.prepend true [] (.inr (.inr (.inr returned))) (.body (.nil (.inr unit)))
    · simp [returned] at noReturn
    · exact result.finish returned stops true []
  | false =>
    cases value : facts.hasValue with
    | true => exact result.value returned value (by simpa [BodyFacts.singleton, returned, value] using same)
    | false =>
      have unit : control.returnType = .unit := by simpa [BodyFacts.singleton, returned, value] using same.symm
      exact result.prepend true [] (.inr (.inr (.inl value))) (.body (.nil (.inr unit)))

private structure BodyResult (source : TypedSource) (expressionSyntax : ExpressionId → Prop)
    (control : ControlContext) (context : SourceSemantics.Context) (ids : List StatementId) (facts : BodyFacts) : Prop where
  tree : ∀ mode, (mode = false ∨ facts.type = control.returnType) →
    BodySyntax source expressionSyntax context mode ids control.returnType

private structure ItemResult (source : TypedSource) (expressionSyntax : ExpressionId → Prop)
    (context final : SourceSemantics.Context) (item : ForItemForm) : Prop where
  header : ∀ rest, GenericForHeader.Syntax source expressionSyntax final rest →
    GenericForHeader.Syntax source expressionSyntax context (item :: rest)
  initial : ∀ rest condition post statements expected,
    GenericImperativeMatch.Syntax source expressionSyntax final (.initializers rest condition post statements) expected →
    GenericImperativeMatch.Syntax source expressionSyntax context (.initializers (item :: rest) condition post statements) expected

private structure ItemsResult (source : TypedSource) (expressionSyntax : ExpressionId → Prop)
    (context final : SourceSemantics.Context) (items : List ForItemForm) : Prop where
  header : GenericForHeader.Syntax source expressionSyntax context items
  initial : ∀ condition post statements expected,
    GenericImperativeMatch.Syntax source expressionSyntax final (.initializers [] condition post statements) expected →
    GenericImperativeMatch.Syntax source expressionSyntax context (.initializers items condition post statements) expected

private def CaseResult (source : TypedSource) (expressionSyntax : ExpressionId → Prop)
    (control : ControlContext) (context : SourceSemantics.Context) (type : TypeSystem.Ty) (arm : TypedMatchCase) : Prop :=
  ∀ binders arity armContext, TypedMatchPatternHasType context arm.pattern type binders arity →
    BindersExtend source.owner context binders armContext →
    BodySyntax source expressionSyntax armContext false arm.body control.returnType

private def CasesResult (source : TypedSource) (expressionSyntax : ExpressionId → Prop)
    (control : ControlContext) (context : SourceSemantics.Context) (type : TypeSystem.Ty) (arms : List TypedMatchCase) : Prop :=
  ∀ arm ∈ arms, CaseResult source expressionSyntax control context type arm

private theorem expression_node {source : TypedSource} {context : SourceSemantics.Context}
    {id : ExpressionId} {type : TypeSystem.Ty} (unique : NodeOccurrencesUnique source)
    (typed : ExpressionHasType source context id type) :
    ∃ node, source.lookupExpression? id = some node ∧ node.type = type ∧ ExpressionHasType source context id node.type := by
  cases typed with
  | intro contains form raw rawWF outputWF requirements =>
    exact ⟨_, lookupExpression?_complete unique contains, rfl,
      .intro contains form raw rawWF outputWF requirements⟩

private theorem match_children {source : TypedSource} {expressionSyntax : ExpressionId → Prop}
    {control : ControlContext} {context : SourceSemantics.Context} {type : TypeSystem.Ty}
    {arms : List TypedMatchCase} {fallback : Option (List StatementId)}
    (cases : CasesResult source expressionSyntax control context type arms)
    (default : ∀ statements, fallback = some statements → BodySyntax source expressionSyntax context false statements control.returnType) :
    ∀ request childContext, GenericMatchChildren.ContextFor source context type arms fallback request childContext →
      BodySyntax source expressionSyntax childContext false request.statements control.returnType := by
  intro request childContext located
  cases located with
  | arm member statements typed extended =>
    rw [statements]
    exact cases _ member _ _ _ typed extended
  | default statements => exact default _ statements

/-- Static source typing and its finite leaf/allocator/stopping receipts
construct the existing Syntax. The original annotation is kept explicitly;
completion is not used to infer universal stopping. -/
theorem syntax_of_typed {source : TypedSource} {expressionSyntax : ExpressionId → Prop}
    {control : ControlContext} {context final : SourceSemantics.Context} {ids : List StatementId}
    {facts : BodyFacts} {typed : StatementsHaveType source control context ids final facts} {ready : Bool}
    (unique : NodeOccurrencesUnique source) (receipt : BodyReceipts source expressionSyntax typed ready)
    (same : facts.type = control.returnType) :
    GenericImperativeMatch.Syntax source expressionSyntax context (.statements true ids) control.returnType := by
  have result : BodyResult source expressionSyntax control context ids facts := by
    apply BodyReceipts.rec (t := receipt)
      (motive_1 := fun {control context id final facts} _ ready _ => StatementSyntax source expressionSyntax control context id final facts ready)
      (motive_2 := fun {control context ids final facts} _ ready _ => BodyResult source expressionSyntax control context ids facts)
      (motive_3 := fun {control context item final} _ _ => ItemResult source expressionSyntax context final item)
      (motive_4 := fun {control context items final} _ _ => ItemsResult source expressionSyntax context final items)
      (motive_5 := fun {control context type arm facts} _ ready _ => CaseResult source expressionSyntax control context type arm)
      (motive_6 := fun {control context type arms facts} _ ready _ => CasesResult source expressionSyntax control context type arms)
    case letUninitialized =>
      intros
      rename_i binderReceipt
      refine ⟨?_, ?_, ?_⟩
      · intro mode rest _ tail
        exact .uninitialized (lookupStatement?_complete unique (by assumption)) (by assumption)
          binderReceipt.1 binderReceipt.2.1 (by assumption) binderReceipt.2.2 tail
      · intros; contradiction
      · intros; contradiction
    case letInitialized =>
      intros
      rename_i binderReceipt value
      obtain ⟨node, found, sourceType, typed⟩ := expression_node unique (by assumption)
      refine ⟨?_, ?_, ?_⟩
      · intro mode rest _ tail
        exact .initialized (lookupStatement?_complete unique (by assumption)) (by assumption)
          binderReceipt.1 binderReceipt.2.1 (by assumption) binderReceipt.2.2 found sourceType typed value tail
      · intros; contradiction
      · intros; contradiction
    case returnUnit =>
      intros
      rename_i control context id node contains form unit annotation
      have root : ∀ mode rest, BodySyntax source expressionSyntax context mode (id :: rest) control.returnType := by
        intro mode rest
        rw [unit]
        exact .body (.returnUnit rest (lookupStatement?_complete unique contains) form (annotation.trans unit))
      exact ⟨fun mode rest _ _ => root mode rest, fun _ _ mode rest => root mode rest, by intros; contradiction⟩
    case returnValue =>
      intros
      rename_i valueSyntax
      obtain ⟨node, found, sourceType, typed⟩ := expression_node unique (by assumption)
      refine ⟨?_, ?_, ?_⟩
      · intro mode rest _ _
        exact .body (.returnValue rest (lookupStatement?_complete unique (by assumption)) (by assumption)
          (by assumption) found sourceType typed valueSyntax)
      · intro _ _ mode rest
        exact .body (.returnValue rest (lookupStatement?_complete unique (by assumption)) (by assumption)
          (by assumption) found sourceType typed valueSyntax)
      · intros; contradiction
    case expressionValue =>
      intros
      rename_i actualControl actualContext id originalNode expression type contains form originalTyped annotation valueSyntax
      obtain ⟨node, found, sourceType, typed⟩ := expression_node unique originalTyped
      refine ⟨?_, ?_, ?_⟩
      · intro mode rest allowed tail
        exact .discard (semicolon := false) (expressionNode := node) (lookupStatement?_complete unique contains) form
          (by rcases allowed with rfl | nonempty | impossible | impossible
              · rfl
              · simp [List.isEmpty_eq_false_iff.mpr nonempty]
              · contradiction
              · contradiction)
          (annotation.trans sourceType.symm) found typed valueSyntax tail
      · intros; contradiction
      · intro _ _ same
        exact .body (.tail (lookupStatement?_complete unique (by assumption)) (by assumption)
          (annotation.trans same) found (sourceType.trans same) typed valueSyntax)
    case expressionDiscard =>
      intros
      rename_i valueSyntax
      obtain ⟨node, found, sourceType, typed⟩ := expression_node unique (by assumption)
      refine ⟨?_, ?_, ?_⟩
      · intro mode rest _ tail
        exact .discard (lookupStatement?_complete unique (by assumption)) (by assumption) rfl (by assumption) found typed valueSyntax tail
      · intros; contradiction
      · intros; contradiction
    case assignValue =>
      intros
      rename_i leaf
      refine ⟨?_, ?_, ?_⟩
      · intro mode rest _ tail
        exact .assign (lookupStatement?_complete unique (by assumption)) (by assumption)
          leaf.projections leaf.writable leaf.right leaf.profile leaf.children tail
      · intros; contradiction
      · intros; contradiction
    case assignBitNot =>
      intros
      rename_i leaf
      refine ⟨?_, ?_, ?_⟩
      · intro mode rest _ tail
        exact .bitNot (lookupStatement?_complete unique (by assumption)) (by assumption)
          leaf.writable leaf.bare leaf.profile tail
      · intros; contradiction
      · intros; contradiction
    case ifWithoutElse =>
      intros
      rename_i conditionSyntax bodyReceipt bodyIH
      obtain ⟨node, found, bool, typed⟩ := expression_node unique (by assumption)
      refine ⟨?_, ?_, ?_⟩
      · intro mode rest _ tail
        exact .ifThen (lookupStatement?_complete unique (by assumption)) (by assumption) (by assumption)
          found bool typed conditionSyntax (bodyIH.tree false (.inl rfl)) (.body (.nil (.inl rfl))) tail
      · intros; contradiction
      · intros; contradiction
    case ifWithElse =>
      intros
      rename_i actualControl actualContext leftFinal rightFinal id originalNode condition left right leftFacts rightFacts contains form conditionTyped leftTyped rightTyped annotation leftReady rightReady conditionSyntax leftReceipt rightReceipt admitted leftIH rightIH
      obtain ⟨node, found, bool, typed⟩ := expression_node unique conditionTyped
      have terminal : (leftFacts.sawReturn && rightFacts.sawReturn) = true → (leftReady && rightReady) = true →
          ∀ mode rest, BodySyntax source expressionSyntax actualContext mode (id :: rest) actualControl.returnType := by
        intro returned available mode rest
        rcases Bool.and_eq_true_iff.mp available with ⟨leftAvailable, rightAvailable⟩
        exact .terminalIf unique (lookupStatement?_complete unique contains) form
          (by simpa [returned] using annotation) found bool typed conditionSyntax
          (leftIH.tree false (.inl rfl)) (rightIH.tree false (.inl rfl))
          (GenericLexicalStatements.Stopped.of_source (leftReceipt.stopping unique leftAvailable))
          (GenericLexicalStatements.Stopped.of_source (rightReceipt.stopping unique rightAvailable))
      refine ⟨?_, terminal, ?_⟩
      · intro mode rest _ tail
        by_cases unit : actualControl.returnType = .unit
        · exact .ifThen (lookupStatement?_complete unique contains) form (by simpa [unit] using annotation)
            found bool typed conditionSyntax (leftIH.tree false (.inl rfl)) (rightIH.tree false (.inl rfl)) tail
        · by_cases returned : (leftFacts.sawReturn && rightFacts.sawReturn) = true
          · rcases admitted with same | noReturn | ⟨leftAvailable, rightAvailable⟩
            · exact False.elim (unit same)
            · simp [returned] at noReturn
            · exact terminal returned (Bool.and_eq_true_iff.mpr ⟨leftAvailable, rightAvailable⟩) mode rest
          · have noReturn : (leftFacts.sawReturn && rightFacts.sawReturn) = false := by cases flag : (leftFacts.sawReturn && rightFacts.sawReturn) <;> simp_all
            exact .ifThen (lookupStatement?_complete unique contains) form (by simpa [noReturn] using annotation)
              found bool typed conditionSyntax (leftIH.tree false (.inl rfl)) (rightIH.tree false (.inl rfl)) tail
      · intro noReturn value _
        simp_all
    case block =>
      intros
      rename_i actualControl actualContext innerFinal id node statements facts contains form bodyTyped annotation ready bodyReceipt bodyIH
      refine ⟨?_, ?_, ?_⟩
      · intro mode rest _ tail
        exact .scopedBlock (lookupStatement?_complete unique contains) form (bodyIH.tree false (.inl rfl)) tail
      · intro returned available mode rest
        exact .terminalBlock unique (lookupStatement?_complete unique contains) form
          (annotation.trans (returned_type bodyTyped returned)) (bodyIH.tree false (.inl rfl))
          (GenericLexicalStatements.Stopped.of_source (bodyReceipt.stopping unique available))
      · intro noReturn value _
        simp_all
    case matchWithoutDefault =>
      intros
      rename_i actualControl actualContext id originalNode resolution type facts summary contains form absent scrutineeTyped casesTyped requirements exhaustive merged annotation ready scrutineeSyntax casesReceipt hidden ordinary casesIH
      obtain ⟨node, found, same, typed⟩ := expression_node unique scrutineeTyped
      have sourceType : originalNode.type = .unit ∨ originalNode.type = actualControl.returnType := by
        cases flag : allBodiesSawReturn facts <;> simp_all
      have children := match_children casesIH (fallback := resolution.defaultBody) (by intro body same; simp [absent] at same)
      refine ⟨?_, ?_, ?_⟩
      · intro mode rest _ tail
        apply GenericImperativeMatch.Syntax.matchWith (control := actualControl) (caseFacts := facts)
          (lookupStatement?_complete unique contains) form sourceType found typed scrutineeSyntax
          (by simpa [same] using casesTyped) (by intro body same; simp [absent] at same) hidden ordinary
          (by simpa [same] using children) tail
      · intros; contradiction
      · intro noReturn value _
        simp_all
    case matchWithDefault =>
      intros
      rename_i actualControl actualContext defaultFinal id originalNode resolution fallback type facts defaultFacts summary contains form present scrutineeTyped casesTyped defaultTyped requirements merged annotation ready defaultReady scrutineeSyntax casesReceipt fallbackReceipt hidden ordinary casesIH defaultIH
      obtain ⟨node, found, same, typed⟩ := expression_node unique scrutineeTyped
      have sourceType : originalNode.type = .unit ∨ originalNode.type = actualControl.returnType := by
        cases flag : (allBodiesSawReturn facts && defaultFacts.sawReturn) <;> simp_all
      have default : ∀ statements, resolution.defaultBody = some statements →
          ∃ finalContext facts, StatementsHaveType source actualControl actualContext statements finalContext facts := by
        intro statements equal
        cases Option.some.inj (present.symm.trans equal)
        exact ⟨_, _, defaultTyped⟩
      have children := match_children casesIH (fallback := resolution.defaultBody) (by
        intro statements equal
        cases Option.some.inj (present.symm.trans equal)
        exact defaultIH.tree false (.inl rfl))
      refine ⟨?_, ?_, ?_⟩
      · intro mode rest _ tail
        exact .matchWith (lookupStatement?_complete unique contains) form sourceType found typed scrutineeSyntax
          (by simpa [same] using casesTyped) default hidden ordinary (by simpa [same] using children) tail
      · intro _ available mode rest
        rcases Bool.and_eq_true_iff.mp available with ⟨casesAvailable, defaultAvailable⟩
        have stopped : ReachableStatementContinuations.StoppingStatement source id summary.eraseValue :=
          .matchDefault (lookupStatement?_complete unique contains) form present casesTyped defaultTyped merged
            (casesReceipt.stopping unique casesAvailable) (fallbackReceipt.stopping unique defaultAvailable)
        exact .terminalMatch unique (lookupStatement?_complete unique contains) form sourceType found typed scrutineeSyntax
          (by simpa [same] using casesTyped) default hidden ordinary (by simpa [same] using children)
          (stopped_match (lookupStatement?_complete unique contains) form stopped)
      · intro noReturn value _
        simp_all
    case forLoop =>
      intros
      rename_i initialReceipt conditionSyntax bodyReceipt postReceipt initialIH bodyIH postIH
      obtain ⟨node, found, bool, typed⟩ := expression_node unique (by assumption)
      refine ⟨?_, ?_, ?_⟩
      · intro mode rest _ tail
        exact .forLoop (lookupStatement?_complete unique (by assumption)) (by assumption) (by assumption)
          (initialIH.initial _ _ _ _ (.initializersDone found bool typed conditionSyntax
            (bodyIH.tree false (.inl rfl)) postIH.header)) tail
      · intros; contradiction
      · intros; contradiction
    case whileLoop =>
      intros
      rename_i conditionSyntax bodyReceipt bodyIH
      obtain ⟨node, found, bool, typed⟩ := expression_node unique (by assumption)
      refine ⟨?_, ?_, ?_⟩
      · intro mode rest _ tail
        exact .whileLoop (lookupStatement?_complete unique (by assumption)) (by assumption) found bool typed conditionSyntax
          (bodyIH.tree false (.inl rfl)) tail
      · intros; contradiction
      · intros; contradiction
    case breakStmt =>
      intros
      refine ⟨?_, ?_, ?_⟩
      · intro mode rest _ _
        exact .breaking (lookupStatement?_complete unique (by assumption)) (by assumption)
      · intros; contradiction
      · intros; contradiction
    case continueStmt =>
      intros
      refine ⟨?_, ?_, ?_⟩
      · intro mode rest _ _
        exact .continuing (lookupStatement?_complete unique (by assumption)) (by assumption)
      · intros; contradiction
      · intros; contradiction
    case nil =>
      intros
      exact ⟨fun mode allowed => .body (.nil (by
        rcases allowed with ordinary | same
        · exact .inl ordinary
        · exact .inr same.symm))⟩
    case singleton =>
      intros
      rename_i actualControl actualContext final id facts headTyped ready headReceipt admitted headIH
      refine ⟨?_⟩
      intro mode allowed
      cases mode with
      | false => exact headIH.prepend false [] (.inl rfl) (.body (.nil (.inl rfl)))
      | true =>
        have same := allowed.resolve_left (by decide)
        exact headIH.singleton same (admitted same)
    case cons =>
      intros
      rename_i actualControl actualContext middle final id next rest headFacts tailFacts headTyped tailTyped headReady tailReady headReceipt tailReceipt admitted headIH tailIH
      refine ⟨?_⟩
      intro mode allowed
      cases mode with
      | false => exact headIH.prepend false _ (.inl rfl) (tailIH.tree false (.inl rfl))
      | true =>
        have same := allowed.resolve_left (by decide)
        rcases admitted same with tailMatches | ⟨returns, ready⟩
        · exact headIH.prepend true _ (.inr (.inl (by simp))) (tailIH.tree true (.inr tailMatches))
        · exact headIH.finish returns ready true _
    case letUninitialized =>
      intros
      rename_i leaf
      exact ⟨fun rest tail => .uninitialized leaf.1 leaf.2.1 (by assumption) leaf.2.2 tail,
        fun rest condition post statements expected tail => .initializerUninitialized leaf.1 leaf.2.1 (by assumption) leaf.2.2 tail⟩
    case letInitialized =>
      intros
      rename_i leaf value
      obtain ⟨node, found, same, typed⟩ := expression_node unique (by assumption)
      exact ⟨fun rest tail => .initialized leaf.1 leaf.2.1 (by assumption) leaf.2.2 found same typed value tail,
        fun rest condition post statements expected tail => .initializerInitialized leaf.1 leaf.2.1 (by assumption) leaf.2.2 found same typed value tail⟩
    case expression =>
      intros
      rename_i value
      obtain ⟨node, found, same, typed⟩ := expression_node unique (by assumption)
      exact ⟨fun rest tail => .discard found typed value tail,
        fun rest condition post statements expected tail => .initializerDiscard found typed value tail⟩
    case assignValue =>
      intros
      rename_i leaf
      exact ⟨fun rest tail => .assign leaf.projections leaf.writable leaf.right leaf.profile leaf.children tail,
        fun rest condition post statements expected tail => .initializerAssign leaf.projections leaf.writable leaf.right leaf.profile leaf.children tail⟩
    case assignBitNot =>
      intros
      rename_i leaf
      exact ⟨fun rest tail => .bitNot leaf.writable leaf.bare leaf.profile tail,
        fun rest condition post statements expected tail => .initializerBitNot leaf.writable leaf.bare leaf.profile tail⟩
    case nil => intros; exact ⟨.nil, fun _ _ _ _ tail => tail⟩
    case cons =>
      intros
      rename_i headIH tailIH
      exact ⟨headIH.header _ tailIH.header, fun condition post statements expected tail =>
        headIH.initial _ condition post statements expected (tailIH.initial condition post statements expected tail)⟩
    case intro =>
      intros
      rename_i actualControl parent type arm originalBinders originalArity originalContext final facts pattern extension bodyTyped ready bodyReceipt bodyIH
      intro binders arity armContext typed extended
      have same := pattern_context_eq (source := source) pattern typed extension extended
      rw [← same]
      exact bodyIH.tree false (.inl rfl)
    case nil => intros; intro arm member; cases member
    case cons =>
      intros
      rename_i headIH tailIH
      intro arm member
      rcases List.mem_cons.mp member with rfl | member
      · exact headIH
      · exact tailIH arm member
  exact result.tree true (.inr same)

section Extraction
open Core GenericImperativeMatch
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {reasonAt : ExpressionId → Word}
  {definitions : DataEnvironment} {administrative : Core.Context}

variable {matchCompilation : SourceCoreCompatibleDataMatches.Context}
variable {policy : SourceCoreLoops.Policy}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word}
  {invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}

/-- The sole residual-aware extractor consumes the generated Syntax once.
Original acceptance, full emitted suffixes, source completion and native typing
remain the same receipts; expression and allocation callbacks stay explicit. -/
theorem extraction_of_typed_body (residualMode : Bool) (diagnosticPolicy : AssignmentDiagnosticPolicy) {tracked : Bool}
    (factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy source invalidOperand)
    (matchPolicy : policy.lowerMatch = some (SourceCoreCompatibleDataMatches.lowerWithReasons matchCompilation))
    (matchValues : matchCompilation.values = values)
    (matchDefinitions : matchCompilation.definitions = definitions)
    (matchAllocator : matchCompilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (matchChildStatic : MatchChildStatic matchCompilation source certificates definitions administrative)
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      policy.lowerBinder source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked source scope binder)
    (allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (expressions : ∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = residualMode →
      sourceContext.signatures = values.checked.signatures →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations source scope sourceContext → expressionSyntax id →
      source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
      certificates sourceContext scope id lowered)
    (assignments : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection invalidOperand missingDefault)
    (unaryPolicy : CompatibleBitNotStatements.Policy policy values invalidProjection invalidUnary missingDefault)
    (unique : NodeOccurrencesUnique source)
    (assignmentExpressions : ∀ sourceContext scope fuel id lowered,
      sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = residualMode →
      sourceContext.signatures = values.checked.signatures →
      CompatibleExpressionReads.ScopeDeclarations source scope sourceContext →
      expressionSyntax id → ∀ node, source.lookupExpression? id = some node →
      ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
        certificates sourceContext scope id lowered ∧
        HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
          (LanguageResult.resultType lowered.type) definitions)
    {context : SourceSemantics.Context} {scope : Scope} {statements : List StatementId} {expected : TypeSystem.Ty}
    {finalContext : SourceSemantics.Context} {facts : BodyFacts}
    (typed : StatementsHaveType source { returnType := expected } context statements finalContext facts)
    {ready : Bool} (receipt : BodyReceipts source expressionSyntax typed ready)
    (annotation : facts.type = expected) (completed : BodyCompletes expected facts)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = residualMode)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type nativeType : Ty} {code : Expr} {fellThrough escaped : Word}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope statements type reasonAt fellThrough escaped = .ok code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions) :
    ∃ flow,
      SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements type reasonAt true escaped = .ok flow ∧
      ∃ _extracted : ExtractionFor diagnosticPolicy layouts owner active frame globals onError values source expressionSyntax certificates definitions administrative matchCompilation.solvedRequirements
        context scope (.statements true statements) expected type flow,
      code = LocalControl.finish type (LocalLoop.toControl type flow escaped)
        (if type = .unit then LanguageResult.success .unit else LanguageResult.failure type (.word fellThrough)) ∧
      BodyCompletes expected facts := by
  have syntaxTree := syntax_of_typed unique receipt annotation
  obtain ⟨flow, generated, extracted, same⟩ :=
    GenericImperativeMatch.extraction_of_typed_body_with_residual residualMode diagnosticPolicy factory
      matchPolicy matchValues matchDefinitions matchAllocator matchChildStatic readPolicy binderPolicy allocationPolicy
      expressions assignments unaryPolicy unique assignmentExpressions syntaxTree closed residual sourceSignatures declarations
      projection accepted nativeTyped
  exact ⟨flow, generated, extracted, same, completed⟩
end Extraction

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeMatchSyntaxFactory
