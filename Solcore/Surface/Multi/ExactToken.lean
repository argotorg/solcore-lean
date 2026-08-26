import Solcore.Surface.Multi.Properties

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace

/-- The exact source spelling retained by every ordinary token payload.
Opaque assembly blocks are represented by their structured slice instead. -/
def TokenKind.sourceSpelling? : TokenKind → Option String
  | .hardKeyword keyword => some keyword.spelling
  | .identifier spelling => some spelling
  | .pragmaName kind => some kind.spelling
  | .decimalLiteral spelling _ => some spelling
  | .hexadecimalLiteral spelling _ => some spelling
  | .stringLiteral spelling _ => some spelling
  | .assemblyBlock _ => none
  | .symbol value => some value.spelling

/-- Exact lexical source evidence for every closed token payload shape. -/
def TokenSourceExact (file : WorkspaceFile) (token : Token) : Prop :=
  match token.payload with
  | .hardKeyword keyword =>
      LexicalJudgment.SourceTextAt file token.span.startByte
        token.span.endByte keyword.spelling
  | .identifier spelling =>
      LexicalJudgment.SourceTextAt file token.span.startByte
        token.span.endByte spelling
  | .pragmaName kind =>
      LexicalJudgment.SourceTextAt file token.span.startByte
        token.span.endByte kind.spelling
  | .decimalLiteral spelling _ =>
      LexicalJudgment.SourceTextAt file token.span.startByte
        token.span.endByte spelling
  | .hexadecimalLiteral spelling _ =>
      LexicalJudgment.SourceTextAt file token.span.startByte
        token.span.endByte spelling
  | .stringLiteral spelling _ =>
      LexicalJudgment.SourceTextAt file token.span.startByte
        token.span.endByte spelling
  | .assemblyBlock slice =>
      LexicalJudgment.AssemblySliceAt file token.span.startByte
        token.span.endByte slice
  | .symbol value =>
      LexicalJudgment.SourceTextAt file token.span.startByte
        token.span.endByte value.spelling

/-- The only missing public lexical bridge needed by exact correspondence.
The proof is already contained in `Lexes.retainedTransitions`. -/
theorem Lexes.tokenSourceExact
    {file : WorkspaceFile} {tokens : List Token}
    {comments : List Comment} (lexical : Lexes file tokens comments)
    {token : Token} (member : token ∈ tokens) :
    TokenSourceExact file token := by
  rcases (Lexes.retainedTransitions lexical).1 token member with
      ⟨pendingAssembly, candidateClass, winner⟩ | ⟨endByte, recognized⟩
  · rcases winner with ⟨candidate, maximal⟩
    cases candidate with
    | string endByte retained recognized =>
        rcases recognized with
          ⟨spelling, decoded, quote, contents, sourceText, tokenEq⟩
        have finishEq : token.span.endByte = endByte := by
          have exact := congrArg (fun value : Token => value.span.endByte) tokenEq
          simpa [LexicalJudgment.sourceSpan] using exact
        have payloadEq : token.payload = .stringLiteral spelling decoded :=
          congrArg (fun value : Token => value.payload) tokenEq
        unfold TokenSourceExact
        rw [payloadEq, finishEq]
        exact sourceText
    | pragmaName endByte retained recognized =>
        rcases recognized with ⟨kind, spelling, tokenEq⟩
        have finishEq : token.span.endByte = endByte := by
          have exact := congrArg (fun value : Token => value.span.endByte) tokenEq
          simpa [LexicalJudgment.sourceSpan] using exact
        have payloadEq : token.payload = .pragmaName kind :=
          congrArg (fun value : Token => value.payload) tokenEq
        unfold TokenSourceExact
        rw [payloadEq, finishEq]
        exact spelling.1
    | identifier endByte retained recognized =>
        rcases recognized with
          ⟨text, kind, valid, sourceText, classification, tokenEq⟩
        have finishEq : token.span.endByte = endByte := by
          have exact := congrArg (fun value : Token => value.span.endByte) tokenEq
          simpa [LexicalJudgment.sourceSpan] using exact
        have payloadEq : token.payload = kind :=
          congrArg (fun value : Token => value.payload) tokenEq
        unfold TokenSourceExact
        rw [payloadEq, finishEq]
        cases classification <;> exact sourceText
    | decimal endByte retained recognized =>
        rcases recognized with ⟨digits, valid, sourceText, tokenEq⟩
        have finishEq : token.span.endByte = endByte := by
          have exact := congrArg (fun value : Token => value.span.endByte) tokenEq
          simpa [LexicalJudgment.sourceSpan] using exact
        have payloadEq : token.payload = .decimalLiteral digits digits :=
          congrArg (fun value : Token => value.payload) tokenEq
        unfold TokenSourceExact
        rw [payloadEq, finishEq]
        exact sourceText
    | hexadecimal endByte retained recognized =>
        rcases recognized with ⟨digits, valid, sourceText, tokenEq⟩
        have finishEq : token.span.endByte = endByte := by
          have exact := congrArg (fun value : Token => value.span.endByte) tokenEq
          simpa [LexicalJudgment.sourceSpan] using exact
        have payloadEq : token.payload =
            .hexadecimalLiteral ("0x" ++ digits) digits :=
          congrArg (fun value : Token => value.payload) tokenEq
        unfold TokenSourceExact
        rw [payloadEq, finishEq]
        exact sourceText
    | symbol endByte symbol retained recognized payload =>
        rcases recognized with
          ⟨actual, sourceText, slash, assembly, tokenEq⟩
        have finishEq : token.span.endByte = endByte := by
          have exact := congrArg (fun value : Token => value.span.endByte) tokenEq
          simpa [LexicalJudgment.sourceSpan] using exact
        have payloadEq : token.payload = .symbol actual :=
          congrArg (fun value : Token => value.payload) tokenEq
        unfold TokenSourceExact
        rw [payloadEq, finishEq]
        exact sourceText
  · rcases recognized with ⟨slice, sliceAt, tokenEq⟩
    have finishEq : token.span.endByte = endByte := by
      have exact := congrArg (fun value : Token => value.span.endByte) tokenEq
      simpa [LexicalJudgment.sourceSpan] using exact
    have payloadEq : token.payload = .assemblyBlock slice := by
      exact congrArg (fun value : Token => value.payload) tokenEq
    unfold TokenSourceExact
    rw [payloadEq, finishEq]
    exact sliceAt

/-- Endpoint constraints carried by an expected retained token. -/
inductive TokenSpanConstraint where
  | exact (span : SourceSpan)
  | starts (span : SourceSpan)
  | ends (span : SourceSpan)
  | anchorsEmptyAfter (span : SourceSpan)
  deriving Repr, BEq, DecidableEq

namespace TokenSpanConstraint

def Holds (constraint : TokenSpanConstraint) (token : Token) : Prop :=
  match constraint with
  | .exact span => token.span = span
  | .starts span =>
      token.span.source = span.source ∧
        token.span.startByte = span.startByte
  | .ends span =>
      token.span.source = span.source ∧
        token.span.endByte = span.endByte
  | .anchorsEmptyAfter span =>
      token.span.source = span.source ∧
        token.span.endByte = span.startByte ∧
        span.startByte = span.endByte

def holds (constraint : TokenSpanConstraint) (token : Token) : Bool :=
  match constraint with
  | .exact span => decide (token.span = span)
  | .starts span =>
      decide (token.span.source = span.source) &&
        decide (token.span.startByte = span.startByte)
  | .ends span =>
      decide (token.span.source = span.source) &&
        decide (token.span.endByte = span.endByte)
  | .anchorsEmptyAfter span =>
      decide (token.span.source = span.source) &&
        decide (token.span.endByte = span.startByte) &&
        decide (span.startByte = span.endByte)

@[simp] theorem holds_eq_true_iff
    (constraint : TokenSpanConstraint) (token : Token) :
    constraint.holds token = true ↔ constraint.Holds token := by
  cases constraint <;> simp [holds, Holds, and_assoc]

end TokenSpanConstraint

/-- One expected retained token and every AST endpoint it must realize. -/
structure ExpectedToken where
  kind : TokenKind
  constraints : List TokenSpanConstraint := []
  deriving Repr, BEq, DecidableEq

namespace ExpectedToken

def plain (kind : TokenKind) : ExpectedToken := { kind }

def exact (kind : TokenKind) (span : SourceSpan) : ExpectedToken :=
  { kind, constraints := [.exact span] }

def Matches (expected : ExpectedToken) (actual : Token) : Prop :=
  expected.kind = actual.payload ∧
    ∀ constraint ∈ expected.constraints, constraint.Holds actual

def isMatch (expected : ExpectedToken) (actual : Token) : Bool :=
  decide (expected.kind = actual.payload) &&
    expected.constraints.all (fun constraint => constraint.holds actual)

@[simp] theorem isMatch_eq_true_iff
    (expected : ExpectedToken) (actual : Token) :
    expected.isMatch actual = true ↔ expected.Matches actual := by
  simp [isMatch, Matches, TokenSpanConstraint.holds_eq_true_iff]

def anchorEmptyAfter (span : SourceSpan)
    (token : ExpectedToken) : ExpectedToken :=
  { token with constraints := .anchorsEmptyAfter span :: token.constraints }

end ExpectedToken

/-- One position in the source token language. Optional slots are needed for
grammar terminals whose presence is deliberately erased from the AST. -/
inductive TokenSlot where
  | required (expected : ExpectedToken)
  | optional (expected : ExpectedToken)
  deriving Repr, BEq, DecidableEq

namespace TokenSlot

def isRequired : TokenSlot → Bool
  | .required _ => true
  | .optional _ => false

private def addConstraint
    (constraint : TokenSpanConstraint) : TokenSlot → TokenSlot
  | .required expected => .required {
      expected with constraints := constraint :: expected.constraints }
  | .optional expected => .optional {
      expected with constraints := constraint :: expected.constraints }

/-- Constrain the physical first slot. Generated enclosing plans require this
slot to be mandatory; optional slots occur only in their interior. -/
private def addFirst
    (constraint : TokenSpanConstraint) : List TokenSlot → List TokenSlot
  | [] => []
  | first :: rest => addConstraint constraint first :: rest

/-- Constrain the physical last slot under the same generated-plan invariant. -/
private def addLast (constraint : TokenSpanConstraint)
    (slots : List TokenSlot) : List TokenSlot :=
  (addFirst constraint slots.reverse).reverse

def enclose (span : SourceSpan) (slots : List TokenSlot) : List TokenSlot :=
  addLast (.ends span) (addFirst (.starts span) slots)

/-- Existential source matching. An optional slot may be consumed or skipped;
either way the indexed actual list is consumed in full. -/
inductive ListMatches : List TokenSlot → List Token → Prop where
  | nil : ListMatches [] []
  | required
      {expected : ExpectedToken} {actual : Token}
      {slots : List TokenSlot} {actualTail : List Token}
      (head : expected.Matches actual)
      (tail : ListMatches slots actualTail) :
      ListMatches (.required expected :: slots) (actual :: actualTail)
  | optionalAbsent
      {expected : ExpectedToken} {slots : List TokenSlot}
      {actual : List Token}
      (tail : ListMatches slots actual) :
      ListMatches (.optional expected :: slots) actual
  | optionalPresent
      {expected : ExpectedToken} {actual : Token}
      {slots : List TokenSlot} {actualTail : List Token}
      (head : expected.Matches actual)
      (tail : ListMatches slots actualTail) :
      ListMatches (.optional expected :: slots) (actual :: actualTail)

/-- A complete backtracking decision procedure for `ListMatches`. -/
def listMatches : List TokenSlot → List Token → Bool
  | [], [] => true
  | [], _ :: _ => false
  | .required _ :: _, [] => false
  | .required expected :: slots, actual :: actualTail =>
      expected.isMatch actual && listMatches slots actualTail
  | .optional _ :: slots, [] => listMatches slots []
  | .optional expected :: slots, actuals@(actual :: actualTail) =>
      (expected.isMatch actual && listMatches slots actualTail) ||
        listMatches slots actuals

@[simp] theorem listMatches_eq_true_iff
    (slots : List TokenSlot) (actual : List Token) :
    listMatches slots actual = true ↔ ListMatches slots actual := by
  induction slots generalizing actual with
  | nil =>
      cases actual with
      | nil => exact Iff.intro (fun _ => .nil) (fun _ => rfl)
      | cons head tail =>
          constructor
          · simp [listMatches]
          · intro relation
            cases relation
  | cons slot slots induction =>
      cases slot with
      | required expected =>
          cases actual with
          | nil =>
              constructor
              · simp [listMatches]
              · intro relation
                cases relation
          | cons actual actualTail =>
              rw [listMatches, Bool.and_eq_true,
                ExpectedToken.isMatch_eq_true_iff, induction]
              constructor
              · rintro ⟨head, tail⟩
                exact .required head tail
              · intro relation
                cases relation with
                | required head tail => exact ⟨head, tail⟩
      | optional expected =>
          cases actual with
          | nil =>
              rw [listMatches, induction]
              constructor
              · exact .optionalAbsent
              · intro relation
                cases relation with
                | optionalAbsent tail => exact tail
          | cons actual actualTail =>
              rw [listMatches, Bool.or_eq_true, Bool.and_eq_true,
                ExpectedToken.isMatch_eq_true_iff, induction, induction]
              constructor
              · rintro (⟨head, tail⟩ | tail)
                · exact .optionalPresent head tail
                · exact .optionalAbsent tail
              · intro relation
                cases relation with
                | optionalAbsent tail => exact Or.inr tail
                | optionalPresent head tail => exact Or.inl ⟨head, tail⟩

end TokenSlot

/-- The concrete output of the one-pass AST correspondence visitor. -/
structure TokenPlan where
  slots : List TokenSlot
  deriving Repr, BEq, DecidableEq

namespace TokenPlan

private def lastRequired : TokenSlot → List TokenSlot → Bool
  | last, [] => last.isRequired
  | _, next :: rest => lastRequired next rest

/-- Empty plans and plans whose physical endpoints are mandatory are the only
plans on which unconditional first/last token constraints are sound. -/
def wellAnchored : TokenPlan → Bool
  | ⟨[]⟩ => true
  | ⟨first :: rest⟩ => first.isRequired && lastRequired first rest

def WellAnchored (plan : TokenPlan) : Prop :=
  plan.wellAnchored = true

def empty : TokenPlan := ⟨[]⟩

def append (left right : TokenPlan) : TokenPlan :=
  ⟨left.slots ++ right.slots⟩

def concat (plans : List TokenPlan) : TokenPlan :=
  ⟨plans.flatMap (fun plan => plan.slots)⟩

def plain (kind : TokenKind) : TokenPlan :=
  ⟨[.required (ExpectedToken.plain kind)]⟩

def exact (kind : TokenKind) (span : SourceSpan) : TokenPlan :=
  ⟨[.required (ExpectedToken.exact kind span)]⟩

def optional (kind : TokenKind) : TokenPlan :=
  ⟨[.optional (ExpectedToken.plain kind)]⟩

def enclose (span : SourceSpan) (plan : TokenPlan) : TokenPlan :=
  ⟨TokenSlot.enclose span plan.slots⟩

def commaSeparated : List TokenPlan → TokenPlan
  | [] => empty
  | first :: rest =>
      append first <| concat <| rest.map fun plan =>
        append (plain (.symbol .comma)) plan

def parens (inner : TokenPlan) : TokenPlan :=
  concat [plain (.symbol .leftParen), inner, plain (.symbol .rightParen)]

end TokenPlan

def tokenKindOfPathSpelling (spelling : String) : TokenKind :=
  match HardKeyword.ofString? spelling with
  | some keyword => .hardKeyword keyword
  | none => .identifier spelling

def identifierPlan (identifier : IdentifierOccurrence) : TokenPlan :=
  .exact (.identifier identifier.payload.render) identifier.span

def pathComponentPlan (component : PathComponent) : TokenPlan :=
  .exact (tokenKindOfPathSpelling component.payload.render) component.span

def externalLibraryPlan (library : Located ExternalLibraryName) : TokenPlan :=
  .exact (tokenKindOfPathSpelling library.payload.render) library.span

def qualifiedNamePlan (name : QualifiedName) : TokenPlan :=
  let components := name.payload.components
  .enclose name.span <| .append (identifierPlan components.head) <|
    .concat <| components.tail.map fun component =>
      .append (.plain (.symbol .dot)) (identifierPlan component)

/-- The classifier constraint not recoverable from a token list alone.
In particular, a bare `lib` is relative, `lib.x` is rooted, and every `std`
spelling is standard-rooted. -/
def relativeModuleReferenceShapeExact
    (components : NonemptyList PathComponent) : Prop :=
  let first := components.head.payload.render
  first ≠ "std" ∧ (first ≠ "lib" ∨ components.tail = [])

def relativeModuleReferenceShapeExactBool
    (components : NonemptyList PathComponent) : Bool :=
  let first := components.head.payload.render
  decide (first ≠ "std") &&
    (decide (first ≠ "lib") || decide (components.tail = []))

@[simp] theorem relativeModuleReferenceShapeExactBool_eq_true_iff
    (components : NonemptyList PathComponent) :
    relativeModuleReferenceShapeExactBool components = true ↔
      relativeModuleReferenceShapeExact components := by
  simp [relativeModuleReferenceShapeExactBool,
    relativeModuleReferenceShapeExact, and_or_left]

/-- Failure by design denotes an AST shape that no source reduction
can produce even if it happens to print the same token text. -/
def moduleReferencePlan? (reference : ModuleReference) : Option TokenPlan :=
  let finish (plan : TokenPlan) := some (.enclose reference.span plan)
  match reference.payload with
  | .relative components =>
      if relativeModuleReferenceShapeExactBool components then
        finish <| .append (pathComponentPlan components.head) <|
          .concat <| components.tail.map fun component =>
            .append (.plain (.symbol .dot)) (pathComponentPlan component)
      else
        none
  | .libraryRoot marker tail =>
      if marker.payload = .libraryRoot then
        finish <| .concat [
          .exact (.identifier "lib") marker.span,
          .plain (.symbol .dot),
          pathComponentPlan tail.head,
          .concat <| tail.tail.map fun component =>
            .append (.plain (.symbol .dot)) (pathComponentPlan component)]
      else
        none
  | .standard marker tail =>
      if marker.payload = .standardRoot then
        finish <| .append (.exact (.identifier "std") marker.span) <|
          .concat <| tail.map fun component =>
            .append (.plain (.symbol .dot)) (pathComponentPlan component)
      else
        none
  | .external atMarker library tail =>
      if atMarker.payload = .externalSigil then
        finish <| .concat [
          .exact (.symbol .at) atMarker.span,
          externalLibraryPlan library,
          .plain (.symbol .dot),
          pathComponentPlan tail.head,
          .concat <| tail.tail.map fun component =>
            .append (.plain (.symbol .dot)) (pathComponentPlan component)]
      else
        none

mutual

private def typePlanMeasure (typeExpression : TypeExpr) : Nat :=
  1 + typePayloadPlanMeasure typeExpression.payload

private def typePayloadPlanMeasure : TypeExprPayload → Nat
  | .named _ arguments => 1 + typeArgumentsPlanMeasure arguments
  | .proxy _ inner => 1 + typePlanMeasure inner
  | .function domain codomain =>
      1 + typePlanMeasure domain + typePlanMeasure codomain
  | .tuple elements => 1 + typeListPlanMeasure elements
  | .group inner => 1 + typePlanMeasure inner
  | .comptime _ inner => 1 + typePlanMeasure inner

private def typeArgumentsPlanMeasure :
    Option (NonemptyList TypeExpr) → Nat
  | none => 0
  | some values => typeNonemptyPlanMeasure values

private def typeNonemptyPlanMeasure
    (values : NonemptyList TypeExpr) : Nat :=
  1 + typePlanMeasure values.head + typeListPlanMeasure values.tail

private def typeListPlanMeasure : List TypeExpr → Nat
  | [] => 0
  | head :: tail =>
      1 + typePlanMeasure head + typeListPlanMeasure tail

end

mutual

/-- Grammar-sensitive type visitor. `atomOnly` is used at predicate/class
heads and on the left of an ungrouped arrow. -/
def typeExprPlanAt? (atomOnly : Bool)
    (typeExpression : TypeExpr) : Option TokenPlan :=
  match typeExpression with
  | ⟨span, .named name arguments⟩ => do
      let namePlan := qualifiedNamePlan name
      match arguments with
      | none => some (.enclose span namePlan)
      | some values =>
          let argumentPlans ← nonemptyTypeExprPlans? values
          some (.enclose span
            (.append namePlan (.parens (.commaSeparated argumentPlans))))
  | ⟨span, .proxy marker inner⟩ => do
      let innerPlan ← typeExprPlanAt? true inner
      some (.enclose span
        (.append (.exact (.symbol .at) marker.span) innerPlan))
  | ⟨span, .function domain codomain⟩ =>
      if atomOnly then none else do
        let domainPlan ← typeExprPlanAt? true domain
        let codomainPlan ← typeExprPlanAt? false codomain
        some (.enclose span
          (.concat [domainPlan, .plain (.symbol .arrow), codomainPlan]))
  | ⟨span, .tuple []⟩ => some (.enclose span (.parens .empty))
  | ⟨_, .tuple [_]⟩ => none
  | ⟨span, .tuple (first :: second :: rest)⟩ => do
      let plans ← typeExprPlans? (first :: second :: rest)
      some (.enclose span (.parens (.commaSeparated plans)))
  | ⟨span, .group inner⟩ => do
      let innerPlan ← typeExprPlanAt? false inner
      some (.enclose span (.parens innerPlan))
  | ⟨span, .comptime marker inner⟩ =>
      if !atomOnly && marker.payload = .comptimeModifier then do
        let innerPlan ← typeExprPlanAt? false inner
        some (.enclose span (.append
          (.exact (.identifier ContextualKeyword.comptimeKw.spelling)
            marker.span) innerPlan))
      else
        none
termination_by typePlanMeasure typeExpression
decreasing_by
  all_goals simp_all [typePlanMeasure, typePayloadPlanMeasure,
    typeArgumentsPlanMeasure, typeNonemptyPlanMeasure,
    typeListPlanMeasure] <;> omega

def typeExprPlans? : List TypeExpr → Option (List TokenPlan)
  | [] => some []
  | head :: tail => do
      let headPlan ← typeExprPlanAt? false head
      let tailPlans ← typeExprPlans? tail
      pure (headPlan :: tailPlans)
termination_by values => typeListPlanMeasure values
decreasing_by
  all_goals simp_all [typeListPlanMeasure] <;> omega

def nonemptyTypeExprPlans?
    (values : NonemptyList TypeExpr) : Option (List TokenPlan) := do
  let headPlan ← typeExprPlanAt? false values.head
  let tailPlans ← typeExprPlans? values.tail
  pure (headPlan :: tailPlans)
termination_by typeNonemptyPlanMeasure values
decreasing_by
  all_goals simp_all [typeNonemptyPlanMeasure] <;> omega
end

def typeExprPlan? (typeExpression : TypeExpr) : Option TokenPlan :=
  typeExprPlanAt? false typeExpression

def typeAtomPlan? (typeExpression : TypeExpr) : Option TokenPlan :=
  typeExprPlanAt? true typeExpression

/-- The one currently identified AST-erased terminal family. Every tail binder
may be preceded by a comma, but `ForallClausePayload.binders` retains only the
binder list. The optional slots preserve both legal spellings without losing
complete-consumption checking. -/
def forallClausePlanWith
    (first : TokenPlan) (rest : List TokenPlan)
    (clause : ForallClause) : TokenPlan :=
  .enclose clause.span <| .concat [
    .plain (.hardKeyword .forallKw),
    first,
    .concat <| rest.map fun binder =>
      .append (.optional (.symbol .comma)) binder,
    .plain (.symbol .dot)]

/-- Context-specific body entry points prevent a braced body and a match-arm
body with the same visible tokens from being interchanged. -/
def bracedBodyPlanWith?
    (statementPlans : List TokenPlan) (body : Body) : Option TokenPlan :=
  match body.payload.origin with
  | .braced openBrace closeBrace =>
      some <| .enclose body.span <| .concat [
        .exact (.symbol .leftBrace) openBrace,
        .concat statementPlans,
        .exact (.symbol .rightBrace) closeBrace]
  | .matchArm _ => none

def armBodyPlanWith?
    (statementPlans : List TokenPlan) (body : Body) : Option TokenPlan :=
  match body.payload.origin, statementPlans with
  | .braced .., _ => none
  | .matchArm _fatArrow, [] =>
      if body.payload.statements = [] then
        some ⟨[]⟩
      else
        none
  | .matchArm _fatArrow, plans@(_ :: _) =>
      some (.enclose body.span (.concat plans))

/-- Attach the empty-body boundary to the already exact fat-arrow token. -/
def matchArmArrowPlan (body : Body) : Option TokenPlan :=
  match body.payload.origin, body.payload.statements with
  | .matchArm fatArrow, [] =>
      some ⟨[.required
        ((ExpectedToken.exact (.symbol .fatArrow) fatArrow).anchorEmptyAfter
          body.span)]⟩
  | .matchArm fatArrow, _ =>
      some (.exact (.symbol .fatArrow) fatArrow)
  | .braced .., _ => none

/-- Reuse the independently executable lexer as the exact byte-partition
check. This binds the otherwise-unused comment argument too. -/
def exactLexicalOutput
    (file : WorkspaceFile) (tokens : List Token)
    (comments : List Comment) : Bool :=
  match lexModule file with
  | .error _ => false
  | .ok lexed =>
      decide (lexed.source = file.id) &&
        decide (lexed.tokens = tokens) &&
        decide (lexed.comments = comments)

def ExactLexicalOutput
    (file : WorkspaceFile) (tokens : List Token)
    (comments : List Comment) : Prop :=
  exactLexicalOutput file tokens comments = true

@[simp] theorem exactLexicalOutput_eq_true_iff
    (file : WorkspaceFile) (tokens : List Token)
    (comments : List Comment) :
    exactLexicalOutput file tokens comments = true ↔
      ExactLexicalOutput file tokens comments := by
  rfl

theorem ExactLexicalOutput.of_lexes
    {file : WorkspaceFile} {tokens : List Token}
    {comments : List Comment}
    (lexical : Lexes file tokens comments) :
    ExactLexicalOutput file tokens comments := by
  unfold ExactLexicalOutput exactLexicalOutput
  rw [lexer_complete lexical]
  simp

/-- Re-running the deterministic lexer is an executable decision procedure for
the independent lexical judgment, including the retained comment sequence. -/
@[simp] theorem exactLexicalOutput_iff_lexes
    (file : WorkspaceFile) (tokens : List Token)
    (comments : List Comment) :
    ExactLexicalOutput file tokens comments ↔ Lexes file tokens comments := by
  constructor
  · intro exact
    unfold ExactLexicalOutput at exact
    change (match lexModule file with
      | .error _ => false
      | .ok lexed =>
          decide (lexed.source = file.id) &&
            decide (lexed.tokens = tokens) &&
            decide (lexed.comments = comments)) = true at exact
    cases execution : lexModule file with
    | error diagnostic =>
        rw [execution] at exact
        contradiction
    | ok lexed =>
        rw [execution] at exact
        simp only [Bool.and_eq_true, decide_eq_true_eq] at exact
        rcases exact with ⟨⟨_, tokenEq⟩, commentEq⟩
        have lexical := (lexer_sound execution).2
        rw [tokenEq, commentEq] at lexical
        exact lexical
  · exact ExactLexicalOutput.of_lexes

/-- Executable final shell. The shape-checking visitor rejects source-impossible AST
shapes before its exact retained-token plan is compared with the lexer output. -/
def exactTokenCorrespondenceWith
    (tokenPlan? : ParsedModuleV1 → Option TokenPlan)
    (file : WorkspaceFile) (tokens : List Token)
    (comments : List Comment) (module : ParsedModuleV1) : Bool :=
  exactLexicalOutput file tokens comments &&
    decide (module.span = SourceSpan.fullFile file) &&
    decide (module.payload.source = file.id) &&
    match tokenPlan? module with
    | none => false
    | some plan => plan.wellAnchored &&
        TokenSlot.listMatches plan.slots tokens

def ExactTokenCorrespondenceWith
    (tokenPlan? : ParsedModuleV1 → Option TokenPlan)
    (file : WorkspaceFile) (tokens : List Token)
    (comments : List Comment) (module : ParsedModuleV1) : Prop :=
  exactTokenCorrespondenceWith tokenPlan? file tokens comments module = true

@[simp] theorem exactTokenCorrespondenceWith_eq_true_iff
    (tokenPlan? : ParsedModuleV1 → Option TokenPlan)
    (file : WorkspaceFile) (tokens : List Token)
    (comments : List Comment) (module : ParsedModuleV1) :
    ExactTokenCorrespondenceWith tokenPlan? file tokens comments module ↔
      ExactLexicalOutput file tokens comments ∧
      module.span = SourceSpan.fullFile file ∧
      module.payload.source = file.id ∧
      ∃ plan, tokenPlan? module = some plan ∧
        plan.WellAnchored ∧ TokenSlot.ListMatches plan.slots tokens := by
  unfold ExactTokenCorrespondenceWith exactTokenCorrespondenceWith
  simp only [Bool.and_eq_true, decide_eq_true_eq,
    exactLexicalOutput_eq_true_iff]
  constructor
  · rintro ⟨⟨⟨lexical, span⟩, source⟩, planned⟩
    split at planned
    · contradiction
    · rename_i plan equation
      have splitPlan : plan.wellAnchored = true ∧
          TokenSlot.listMatches plan.slots tokens = true := by
        simpa only [Bool.and_eq_true] using planned
      rcases splitPlan with ⟨anchored, relation⟩
      exact ⟨lexical, span, source, plan, equation, anchored,
        (TokenSlot.listMatches_eq_true_iff _ _).mp relation⟩
  · rintro ⟨lexical, span, source, plan, equation, anchored, relation⟩
    refine ⟨⟨⟨lexical, span⟩, source⟩, ?_⟩
    rw [equation, Bool.and_eq_true, TokenSlot.listMatches_eq_true_iff]
    exact ⟨anchored, relation⟩

end Solcore.Surface.Multi
