import Solcore.Surface.Multi.Grammar

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Solcore.Workspace
open Grammar

/-- Every chart boundary, including the boundary after logical end of file. -/
abbrev Boundary (tokens : List Token) : Type := Fin (tokens.length + 2)

/-- Every terminal position: retained tokens followed by logical end of file. -/
abbrev TerminalCursor (tokens : List Token) : Type := Fin (tokens.length + 1)

namespace TerminalCursor

/-- Embed a terminal cursor as its boundary before the selected terminal. -/
def beforeBoundary {tokens : List Token}
    (cursor : TerminalCursor tokens) : Boundary tokens :=
  Fin.castLE (Nat.le_succ _) cursor

/-- Select the boundary immediately after one retained or logical terminal. -/
def afterBoundary {tokens : List Token}
    (cursor : TerminalCursor tokens) : Boundary tokens := {
  val := cursor.val + 1
  isLt := Nat.succ_lt_succ cursor.isLt
}

end TerminalCursor

namespace Boundary

/-- The first chart boundary. -/
def start (tokens : List Token) : Boundary tokens := {
  val := 0
  isLt := Nat.zero_lt_succ _
}

/-- The chart boundary after the one logical end-of-file terminal. -/
def afterLogicalEOF (tokens : List Token) : Boundary tokens := {
  val := tokens.length + 1
  isLt := Nat.lt_succ_self (tokens.length + 1)
}

end Boundary

/-- The nearest parser region relevant to guarded productions. -/
inductive GuardContext (tokens : List Token) where
  | plain
  | bracedBody (bodyStart : Boundary tokens)
  | armBody (armBodyStart : Boundary tokens)
  | postfixInvocation (postfixStart : Boundary tokens)
  deriving Repr, BEq, DecidableEq

/-- One production predicted at an origin in its exact guard context. -/
structure ProductionInstanceKey (tokens : List Token) where
  production : ProductionId
  origin : Boundary tokens
  context : GuardContext tokens
  deriving Repr, BEq, DecidableEq

/-- One priority-guard query at an ordered pair of chart boundaries. -/
structure GuardInstanceKey (tokens : List Token) where
  guard : PriorityGuardId
  contextStart : Boundary tokens
  siteCursor : Boundary tokens
  ordered : contextStart.val ≤ siteCursor.val
  deriving Repr, BEq, DecidableEq

/-- One expanded production at a dot position and chart interval. -/
structure DottedItem (tokens : List Token) where
  production : ProductionId
  dot : Fin (production.rhs.length + 1)
  origin : Boundary tokens
  current : Boundary tokens
  deriving Repr, BEq, DecidableEq

/-- A proof-free unguarded scan or completion edge key. -/
inductive PackedEdgeKey (tokens : List Token) where
  | scanned
      (before after : DottedItem tokens)
      (terminalCursor : TerminalCursor tokens)
  | completed
      (waiting finished after : DottedItem tokens)
      (sharedCursor : Boundary tokens)
  deriving Repr, BEq, DecidableEq

/-- One dotted item paired with its exact guard context. -/
structure ContextualItemKey (tokens : List Token) where
  raw : DottedItem tokens
  context : GuardContext tokens
  deriving Repr, BEq, DecidableEq

/-- A proof-free contextual scan or completion edge key. -/
inductive ContextualPackedEdgeKey (tokens : List Token) where
  | scanned
      (before after : ContextualItemKey tokens)
      (terminalCursor : TerminalCursor tokens)
  | completed
      (waiting finished after : ContextualItemKey tokens)
      (sharedCursor : Boundary tokens)
  deriving Repr, BEq, DecidableEq

/-- The definitionally complete contextual item for one root production. -/
def CanonicalCompleteRootItem
    (tokens : List Token)
    (rule : GrammarRuleId)
    (origin finish : Boundary tokens)
    (context : GuardContext tokens) :
    ContextualItemKey tokens := {
  raw := {
    production := ProductionId.root rule
    dot := {
      val := (ProductionId.root rule).rhs.length
      isLt := Nat.lt_succ_self _
    }
    origin := origin
    current := finish
  }
  context := context
}

/-- Select the exact guard context inherited by one predicted production. -/
def descendContext {tokens : List Token}
    (waiting : ContextualItemKey tokens)
    (predicted : ProductionId) : GuardContext tokens :=
  match predicted with
  | .root .postfix =>
      .postfixInvocation waiting.raw.current
  | _ =>
      match waiting.raw.production, predicted.lhs with
      | .seq waitingSite, .aux predictedSite =>
          if waitingSite.site.isAt .body [] &&
              waiting.raw.dot.val == 1 &&
              predictedSite.isAt .body [1] then
            .bracedBody waiting.raw.current
          else if waitingSite.site.isAt .matchArm [] &&
              waiting.raw.dot.val == 3 &&
              predictedSite.isAt .matchArm [3] then
            .armBody waiting.raw.current
          else
            waiting.context
      | _, _ => waiting.context

/-- Select the unique context start allowed by one closed priority guard. -/
private def guardAnchorContextStart?
    {tokens : List Token}
    (productionInstance : ProductionInstanceKey tokens)
    (guard : PriorityGuardId) : Option (Boundary tokens) :=
  match guard with
  | .G01_statementIf => some productionInstance.origin
  | .G02_matchArmBoundary =>
      match productionInstance.context with
      | .armBody armBodyStart => some armBodyStart
      | _ => none
  | .G03_parameterComptime => some productionInstance.origin
  | .G04_letComptime => some productionInstance.origin
  | .G05_typeComptime => some productionInstance.origin
  | .G06_patternComptime => some productionInstance.origin
  | .G07_leadingDotArguments =>
      match productionInstance.context with
      | .postfixInvocation postfixStart => some postfixStart
      | _ => none
  | .G08_terminalExpression =>
      match productionInstance.context with
      | .bracedBody bodyStart => some bodyStart
      | .armBody armBodyStart => some armBodyStart
      | _ => none
  | .G09_genericContext => some productionInstance.origin

/-- Constructive membership decision for the closed guard-cell lists. -/
private def decidableGuardCellMem
    (cell : PriorityGuardId × Polarity) :
    (cells : List (PriorityGuardId × Polarity)) → Decidable (cell ∈ cells)
  | [] => isFalse (by simp)
  | candidate :: rest =>
      if same : cell = candidate then
        isTrue (List.mem_cons.mpr (Or.inl same))
      else
        match decidableGuardCellMem cell rest with
        | isTrue member =>
            isTrue (List.mem_cons_of_mem candidate member)
        | isFalse absent =>
            isFalse (by
              intro member
              rcases List.mem_cons.mp member with equal | inRest
              · exact same equal
              · exact absent inRest)

/-- The exact structural anchor of one grammar-owned priority-guard cell. -/
def GuardAnchor
    {tokens : List Token}
    (productionInstance : ProductionInstanceKey tokens)
    (cell : PriorityGuardId × Polarity)
    (guardInstance : GuardInstanceKey tokens) : Prop :=
  cell ∈ guardOf productionInstance.production ∧
    guardInstance.guard = cell.1 ∧
    guardInstance.siteCursor = productionInstance.origin ∧
    guardAnchorContextStart? productionInstance cell.1 =
      some guardInstance.contextStart

namespace GuardAnchor

/-- A production cell determines at most one structural guard anchor. -/
theorem functional
    {tokens : List Token}
    {productionInstance : ProductionInstanceKey tokens}
    {cell : PriorityGuardId × Polarity}
    {left right : GuardInstanceKey tokens}
    (leftAnchor : GuardAnchor productionInstance cell left)
    (rightAnchor : GuardAnchor productionInstance cell right) :
    left = right := by
  rcases left with ⟨leftGuard, leftStart, leftSite, _leftOrdered⟩
  rcases right with ⟨rightGuard, rightStart, rightSite, _rightOrdered⟩
  rcases leftAnchor with
    ⟨_leftMember, leftGuardEq, leftSiteEq, leftStartEq⟩
  rcases rightAnchor with
    ⟨_rightMember, rightGuardEq, rightSiteEq, rightStartEq⟩
  have guardEq : leftGuard = rightGuard :=
    leftGuardEq.trans rightGuardEq.symm
  have startEq : leftStart = rightStart :=
    Option.some.inj (leftStartEq.symm.trans rightStartEq)
  have siteEq : leftSite = rightSite :=
    leftSiteEq.trans rightSiteEq.symm
  cases guardEq
  cases startEq
  cases siteEq
  rfl

/-- Compute the exact structural anchor of one grammar-owned guard cell. -/
def decide
    {tokens : List Token}
    (productionInstance : ProductionInstanceKey tokens)
    (cell : PriorityGuardId × Polarity) :
    Option (GuardInstanceKey tokens) :=
  letI : Decidable (cell ∈ guardOf productionInstance.production) :=
    decidableGuardCellMem cell (guardOf productionInstance.production)
  if _member : cell ∈ guardOf productionInstance.production then
    match guardAnchorContextStart? productionInstance cell.1 with
    | none => none
    | some contextStart =>
        if ordered : contextStart.val ≤ productionInstance.origin.val then
          some {
            guard := cell.1
            contextStart := contextStart
            siteCursor := productionInstance.origin
            ordered := ordered
          }
        else
          none
  else
    none

/-- The anchor computation succeeds exactly for the structural relation. -/
theorem decide_eq_some_iff
    {tokens : List Token}
    {productionInstance : ProductionInstanceKey tokens}
    {cell : PriorityGuardId × Polarity}
    {guardInstance : GuardInstanceKey tokens} :
    decide productionInstance cell = some guardInstance ↔
      GuardAnchor productionInstance cell guardInstance := by
  rcases guardInstance with
    ⟨guard, contextStart, siteCursor, instanceOrdered⟩
  unfold decide GuardAnchor
  by_cases member : cell ∈ guardOf productionInstance.production
  · cases startResult : guardAnchorContextStart? productionInstance cell.1 with
    | none =>
        simp [member]
    | some start =>
        by_cases ordered : start.val ≤ productionInstance.origin.val
        · simp [member]
          constructor
          · rintro ⟨guardEq, startEq, _startOrdered, siteEq⟩
            exact ⟨guardEq.symm, siteEq.symm, startEq⟩
          · rintro ⟨guardEq, siteEq, startEq⟩
            exact ⟨guardEq.symm, startEq, ordered, siteEq.symm⟩
        · simp [member]
          constructor
          · rintro ⟨_guardEq, _startEq, startOrdered, _siteEq⟩
            exact (ordered startOrdered).elim
          · rintro ⟨_guardEq, siteEq, startEq⟩
            apply (ordered ?_).elim
            have startValEq : start.val = contextStart.val :=
              congrArg Fin.val startEq
            have siteValEq : siteCursor.val =
                productionInstance.origin.val :=
              congrArg Fin.val siteEq
            omega
  · simp [member]

end GuardAnchor

/-- The unfinished or sealed state of one priority-guard computation. -/
inductive GuardMemoState where
  | undecided
  | final (decision : GuardDecision)
  deriving Repr, BEq, DecidableEq

/-- A table of priority-guard states indexed by their structural anchors. -/
abbrev GuardMemo (tokens : List Token) : Type :=
  GuardInstanceKey tokens → GuardMemoState

/-- Every structural guard query has reached a sealed decision. -/
def AllGuardsFinal
    {tokens : List Token}
    (memo : GuardMemo tokens) : Prop :=
  ∀ key : GuardInstanceKey tokens,
    ∃ decision : GuardDecision, memo key = .final decision

namespace GuardWitnessKey

/-- The proof-free production cell and structural anchor retained by a chart. -/
structure Raw (tokens : List Token) where
  productionInstance : ProductionInstanceKey tokens
  guardInstance : GuardInstanceKey tokens
  polarity : Polarity
  deriving Repr, BEq, DecidableEq

/-- A retained guard key names an exact guarded production-table cell. -/
def Valid
    {tokens : List Token}
    (raw : Raw tokens) : Prop :=
  (raw.guardInstance.guard, raw.polarity) ∈
      guardOf raw.productionInstance.production ∧
    GuardAnchor raw.productionInstance
      (raw.guardInstance.guard, raw.polarity) raw.guardInstance

end GuardWitnessKey

/-- The proof-irrelevant subtype of structurally valid retained guard keys. -/
abbrev GuardWitnessKey (tokens : List Token) : Type :=
  { raw : GuardWitnessKey.Raw tokens // GuardWitnessKey.Valid raw }

namespace GuardWitnessKey

/-- Project the guarded production instance through the checked subtype. -/
def productionInstance
    {tokens : List Token}
    (key : GuardWitnessKey tokens) : ProductionInstanceKey tokens :=
  key.val.productionInstance

/-- Project the structural guard instance through the checked subtype. -/
def guardInstance
    {tokens : List Token}
    (key : GuardWitnessKey tokens) : GuardInstanceKey tokens :=
  key.val.guardInstance

/-- Project the guarded production polarity through the checked subtype. -/
def polarity
    {tokens : List Token}
    (key : GuardWitnessKey tokens) : Polarity :=
  key.val.polarity

end GuardWitnessKey

/-- The absent or source-preserving comma between repeated forall binders. -/
inductive OptionalCommaValue where
  | absent
  | present (comma : SourceSpan)

/-- One source-preserving postfix operation before it is folded over a callee. -/
inductive PostfixPartValue where
  | call
      (openParen : SourceSpan)
      (arguments : List Expression)
      (closeParen : SourceSpan)
  | select
      (dot : SourceSpan)
      (field : IdentifierOccurrence)
  | index
      (openBracket : SourceSpan)
      (index : Expression)
      (closeBracket : SourceSpan)

/-- The exact semantic result carrier of each of the seventy-five source rules. -/
def RuleValue : GrammarRuleId → Type
  | .module => ParsedModuleV1
  | .topItem => TopItem
  | .moduleRef => ModuleReference
  | .importDecl => ImportDecl
  | .importEntry => ImportSelectorEntry
  | .hidingClause => HidingClause
  | .exportDecl => ExportDecl
  | .localExportEntry => ExportEntry
  | .remoteExportEntry => RemoteExportEntry
  | .exportItem => ExportItem
  | .constructorSelection => ConstructorSelection
  | .pragmaDecl => PragmaDecl
  | .genericPrefix => GenericPrefix
  | .forallClause => ForallClause
  | .forallBinder => ForallBinder
  | .optionalComma => OptionalCommaValue
  | .predicateList => NonemptyList Predicate
  | .predicate => Predicate
  | .functionSignature => FunctionSignature
  | .functionDecl => FunctionDecl
  | .classMethod => ClassMethodDecl
  | .dataDecl => DataDecl
  | .dataConstructor => DataConstructor
  | .typeAliasDecl => TypeAliasDecl
  | .classDecl => ClassDecl
  | .instanceDecl => InstanceDecl
  | .instanceMethod => FunctionDecl
  | .contractDecl => ContractDecl
  | .contractMember => ContractMember
  | .fieldDecl => FieldDecl
  | .fallbackDecl => FallbackDecl
  | .contractConstructorDecl => ContractConstructorDecl
  | .parameter => Parameter
  | .body => Body
  | .type => TypeExpr
  | .typeAtom => TypeExpr
  | .qualifiedName => QualifiedName
  | .statement => Statement
  | .letStatement => Statement
  | .letBinding => LetBinding
  | .returnStatement => Statement
  | .blockStatement => Statement
  | .breakStatement => Statement
  | .continueStatement => Statement
  | .assemblyStatement => Statement
  | .ifStatement => Statement
  | .forStatement => Statement
  | .forInitItem => ForInitItem
  | .forPostItem => ForPostItem
  | .matchStatement => Statement
  | .matchArm => MatchArm
  | .armStatement => Statement
  | .assignmentStatement => Statement
  | .assignmentOperator => Located AssignmentOperator
  | .expressionStatement => Statement
  | .terminalExpression => Expression
  | .pattern => Pattern
  | .expression => Expression
  | .annotation => Expression
  | .conditional => Expression
  | .logicalOr => Expression
  | .logicalAnd => Expression
  | .equality => Expression
  | .relational => Expression
  | .bitOr => Expression
  | .bitXor => Expression
  | .bitAnd => Expression
  | .additive => Expression
  | .multiplicative => Expression
  | .prefix => Expression
  | .postfix => Expression
  | .postfixPart => PostfixPartValue
  | .atom => Expression
  | .lambda => Expression
  | .literal => Literal

/-- The literal equation tags of `RuleValue`, in definition branch order. -/
def ruleValueEquationTags : List GrammarRuleId := [
  .module, .topItem, .moduleRef, .importDecl, .importEntry,
  .hidingClause, .exportDecl, .localExportEntry, .remoteExportEntry,
  .exportItem, .constructorSelection, .pragmaDecl, .genericPrefix,
  .forallClause, .forallBinder, .optionalComma, .predicateList,
  .predicate, .functionSignature, .functionDecl, .classMethod, .dataDecl,
  .dataConstructor, .typeAliasDecl, .classDecl, .instanceDecl,
  .instanceMethod, .contractDecl, .contractMember, .fieldDecl,
  .fallbackDecl, .contractConstructorDecl, .parameter, .body, .type,
  .typeAtom, .qualifiedName, .statement, .letStatement, .letBinding,
  .returnStatement, .blockStatement, .breakStatement, .continueStatement,
  .assemblyStatement, .ifStatement, .forStatement, .forInitItem,
  .forPostItem, .matchStatement, .matchArm, .armStatement,
  .assignmentStatement, .assignmentOperator, .expressionStatement,
  .terminalExpression, .pattern, .expression, .annotation, .conditional,
  .logicalOr, .logicalAnd, .equality, .relational, .bitOr, .bitXor,
  .bitAnd, .additive, .multiplicative, .prefix, .postfix, .postfixPart,
  .atom, .lambda, .literal
]

/-- The semantic carrier has one explicit equation for every source rule. -/
theorem ruleValue_allGrammarRuleIds_exhaustive :
    ruleValueEquationTags = allGrammarRuleIds := by
  rfl

/-- The symbol selected by the dot of one incomplete item. -/
def NextSymbol {tokens : List Token}
    (item : DottedItem tokens) (symbol : GrammarSymbol) : Prop :=
  item.dot.val < item.production.rhs.length ∧
    item.production.rhs[item.dot.val]? = some symbol

/-- An item whose dot is exactly at the end of its production. -/
def CompleteItem {tokens : List Token} (item : DottedItem tokens) : Prop :=
  item.dot.val = item.production.rhs.length

/-- The exact structural update that advances one item's dot and cursor. -/
def AdvanceItem {tokens : List Token}
    (before : DottedItem tokens) (next : Boundary tokens)
    (after : DottedItem tokens) : Prop :=
  after.production = before.production ∧
    after.dot.val = before.dot.val + 1 ∧
    after.origin = before.origin ∧
    after.current = next

/-- A dot at zero selects the empty right-hand-side prefix. -/
theorem prefix_zero_layout
    {tokens : List Token}
    (item : DottedItem tokens)
    (zero : item.dot.val = 0) :
    [] = item.production.rhs.take item.dot.val := by
  rw [zero, List.take_zero]

/-- Scanning the next terminal appends exactly that terminal to the prefix. -/
theorem prefix_scan_layout
    {tokens : List Token}
    (before after : DottedItem tokens)
    (terminal : TerminalSymbol)
    (nextBoundary : Boundary tokens)
    (next : NextSymbol before (GrammarSymbol.terminal terminal))
    (advance : AdvanceItem before nextBoundary after) :
    before.production.rhs.take before.dot.val ++
        [GrammarSymbol.terminal terminal] =
      after.production.rhs.take after.dot.val := by
  rcases next with ⟨_inRange, lookup⟩
  rcases advance with ⟨production, dot, _origin, _current⟩
  have rhs : after.production.rhs = before.production.rhs :=
    congrArg ProductionId.rhs production
  rw [dot, rhs, List.take_add_one, lookup]
  rfl

/-- Completing the next nonterminal appends exactly that symbol to the prefix. -/
theorem prefix_complete_layout
    {tokens : List Token}
    (waiting finished after : DottedItem tokens)
    (next : NextSymbol waiting
      (GrammarSymbol.nonterminal finished.production.lhs))
    (advance : AdvanceItem waiting finished.current after) :
    waiting.production.rhs.take waiting.dot.val ++
        [GrammarSymbol.nonterminal finished.production.lhs] =
      after.production.rhs.take after.dot.val := by
  rcases next with ⟨_inRange, lookup⟩
  rcases advance with ⟨production, dot, _origin, _current⟩
  have rhs : after.production.rhs = waiting.production.rhs :=
    congrArg ProductionId.rhs production
  rw [dot, rhs, List.take_add_one, lookup]
  rfl

/-- A complete item's right-hand-side prefix is the full right-hand side. -/
theorem prefix_full_layout
    {tokens : List Token}
    (item : DottedItem tokens)
    (complete : CompleteItem item) :
    item.production.rhs.take item.dot.val = item.production.rhs := by
  unfold CompleteItem at complete
  rw [complete, List.take_length]

/-- The canonical root item is definitionally complete. -/
theorem canonicalCompleteRootItem_complete
    {tokens : List Token}
    (rule : GrammarRuleId)
    (origin finish : Boundary tokens)
    (context : GuardContext tokens) :
    CompleteItem
      (CanonicalCompleteRootItem tokens rule origin finish context).raw := by
  rfl

/-- The parser's terminal stream consists of retained tokens and logical EOF. -/
inductive TerminalStreamValue where
  | retained (token : Token)
  | endOfFile
  deriving Repr, BEq, DecidableEq

/-- Every retained token is valid for the file that owns the token stream. -/
def TokensOwnedBy (file : WorkspaceFile) (tokens : List Token) : Prop :=
  ∀ token, token ∈ tokens → token.span.ValidFor file

/-- Exact lookup in the retained-token stream extended by one logical EOF. -/
inductive TerminalAt
    (file : WorkspaceFile)
    (tokens : List Token) :
    TerminalCursor tokens → TerminalStreamValue → SourceSpan → Prop where
  | retained
      (cursor : TerminalCursor tokens)
      (token : Token)
      (inRange : cursor.val < tokens.length)
      (lookup : tokens[cursor.val]? = some token)
      (valid : token.span.ValidFor file) :
      TerminalAt file tokens cursor (.retained token) token.span
  | endOfFile
      (cursor : TerminalCursor tokens)
      (atEnd : cursor.val = tokens.length) :
      TerminalAt file tokens cursor .endOfFile {
        source := file.id
        startByte := file.content.utf8ByteSize
        endByte := file.content.utf8ByteSize
      }

/-- Exact agreement between one grammar terminal and one terminal-stream value. -/
def TerminalMatches : TerminalSymbol → TerminalStreamValue → Prop
  | .hardKeyword keyword, .retained token =>
      token.payload = .hardKeyword keyword
  | .contextualKeyword keyword, .retained token =>
      token.payload = .identifier keyword.spelling
  | .pragmaName kind, .retained token =>
      token.payload = .pragmaName kind
  | .symbol symbol, .retained token =>
      token.payload = .symbol symbol
  | .category .identifier, .retained token =>
      ∃ text parsed,
        token.payload = .identifier text ∧
          Identifier.parse text = some parsed
  | .category .pathComponent, .retained token =>
      (∃ text parsed,
        token.payload = .identifier text ∧
          PathSegment.parse text = some parsed) ∨
      (∃ keyword parsed,
        token.payload = .hardKeyword keyword ∧
          PathSegment.parse keyword.spelling = some parsed)
  | .category .decimalLiteral, .retained token =>
      ∃ spelling digits,
        token.payload = .decimalLiteral spelling digits
  | .category .hexadecimalLiteral, .retained token =>
      ∃ spelling digits,
        token.payload = .hexadecimalLiteral spelling digits
  | .category .stringLiteral, .retained token =>
      ∃ spelling decoded,
        token.payload = .stringLiteral spelling decoded
  | .category .assemblyBlock, .retained token =>
      ∃ slice, token.payload = .assemblyBlock slice
  | .endOfFile, .endOfFile => True
  | _, _ => False

/-- A terminal-stream value together with its exact lookup and match evidence. -/
structure MatchedTerminal
    (file : WorkspaceFile)
    (tokens : List Token)
    (terminal : TerminalSymbol) where
  cursor : TerminalCursor tokens
  value : TerminalStreamValue
  span : SourceSpan
  «at» : TerminalAt file tokens cursor value span
  «matches» : TerminalMatches terminal value
  deriving Repr, DecidableEq

instance {file : WorkspaceFile} {tokens : List Token}
    {terminal : TerminalSymbol} :
    BEq (MatchedTerminal file tokens terminal) :=
  ⟨fun left right => decide (left = right)⟩

namespace PackedEdgeKey

/-- Exact structural validity for an unguarded scanned or completed edge. -/
def Valid
    (file : WorkspaceFile)
    (tokens : List Token) :
    PackedEdgeKey tokens → Prop
  | .scanned before after terminalCursor =>
      ∃ terminal value span,
        NextSymbol before (GrammarSymbol.terminal terminal) ∧
          terminalCursor.beforeBoundary = before.current ∧
          TerminalAt file tokens terminalCursor value span ∧
          TerminalMatches terminal value ∧
          AdvanceItem before terminalCursor.afterBoundary after
  | .completed waiting finished after sharedCursor =>
      ∃ symbol,
        NextSymbol waiting (GrammarSymbol.nonterminal symbol) ∧
          CompleteItem finished ∧
          finished.production.lhs = symbol ∧
          waiting.current = sharedCursor ∧
          finished.origin = sharedCursor ∧
          AdvanceItem waiting finished.current after

end PackedEdgeKey

/-- Checked Type witness for one valid scanned edge. -/
structure ScannedEdgeWitness
    (file : WorkspaceFile)
    (tokens : List Token)
    (before after : DottedItem tokens)
    (cursor : TerminalCursor tokens) : Type where
  terminal : TerminalSymbol
  matched : MatchedTerminal file tokens terminal
  sameCursor : matched.cursor = cursor
  next : NextSymbol before (GrammarSymbol.terminal terminal)
  atCurrent : cursor.beforeBoundary = before.current
  advance : AdvanceItem before matched.cursor.afterBoundary after
  deriving Repr, DecidableEq

instance {file : WorkspaceFile} {tokens : List Token}
    {before after : DottedItem tokens} {cursor : TerminalCursor tokens} :
    BEq (ScannedEdgeWitness file tokens before after cursor) :=
  ⟨fun left right => decide (left = right)⟩

/-- Checked Type witness for one valid completed edge. -/
structure CompletedEdgeWitness
    (tokens : List Token)
    (waiting finished after : DottedItem tokens)
    (shared : Boundary tokens) : Type where
  next : NextSymbol waiting
    (GrammarSymbol.nonterminal finished.production.lhs)
  complete : CompleteItem finished
  waitingAtShared : waiting.current = shared
  finishedAtShared : finished.origin = shared
  advance : AdvanceItem waiting finished.current after
  deriving Repr, DecidableEq

instance {tokens : List Token}
    {waiting finished after : DottedItem tokens} {shared : Boundary tokens} :
    BEq (CompletedEdgeWitness tokens waiting finished after shared) :=
  ⟨fun left right => decide (left = right)⟩

/-- A scanned edge is valid exactly when its checked Type witness is inhabited. -/
theorem packedEdge_scanned_valid_iff
    {file : WorkspaceFile}
    {tokens : List Token}
    {before after : DottedItem tokens}
    {cursor : TerminalCursor tokens} :
    PackedEdgeKey.Valid file tokens (.scanned before after cursor) ↔
      Nonempty (ScannedEdgeWitness file tokens before after cursor) := by
  constructor
  · rintro ⟨terminal, value, span, next, atCurrent,
      terminalAt, terminalMatches, advance⟩
    exact ⟨{
      terminal := terminal
      matched := {
        cursor := cursor
        value := value
        span := span
        «at» := terminalAt
        «matches» := terminalMatches
      }
      sameCursor := rfl
      next := next
      atCurrent := atCurrent
      advance := advance
    }⟩
  · rintro ⟨witness⟩
    rcases witness with
      ⟨terminal, matched, sameCursor, next, atCurrent, matchedAdvance⟩
    have terminalAt : TerminalAt file tokens cursor
        matched.value matched.span := by
      rw [← sameCursor]
      exact matched.at
    have afterBoundaryEq : matched.cursor.afterBoundary =
        cursor.afterBoundary :=
      congrArg TerminalCursor.afterBoundary sameCursor
    have advance : AdvanceItem before cursor.afterBoundary after := by
      rw [← afterBoundaryEq]
      exact matchedAdvance
    exact ⟨terminal, matched.value, matched.span, next, atCurrent,
      terminalAt, matched.matches, advance⟩

/-- A completed edge is valid exactly when its checked Type witness is inhabited. -/
theorem packedEdge_completed_valid_iff
    {file : WorkspaceFile}
    {tokens : List Token}
    {waiting finished after : DottedItem tokens}
    {shared : Boundary tokens} :
    PackedEdgeKey.Valid file tokens
        (.completed waiting finished after shared) ↔
      Nonempty
        (CompletedEdgeWitness tokens waiting finished after shared) := by
  constructor
  · rintro ⟨symbol, next, complete, lhs, waitingAtShared,
      finishedAtShared, advance⟩
    have exactNext : NextSymbol waiting
        (GrammarSymbol.nonterminal finished.production.lhs) := by
      rw [lhs]
      exact next
    exact ⟨{
      next := exactNext
      complete := complete
      waitingAtShared := waitingAtShared
      finishedAtShared := finishedAtShared
      advance := advance
    }⟩
  · rintro ⟨witness⟩
    exact ⟨finished.production.lhs, witness.next, witness.complete, rfl,
      witness.waitingAtShared, witness.finishedAtShared, witness.advance⟩

/-- The proof-irrelevant subtype of structurally valid unguarded edges. -/
abbrev PackedEdge (file : WorkspaceFile) (tokens : List Token) : Type :=
  { key : PackedEdgeKey tokens // PackedEdgeKey.Valid file tokens key }

namespace ContextualPackedEdgeKey

/-- Erase contexts from a contextual edge while preserving its raw edge key. -/
def rawProjection {tokens : List Token} :
    ContextualPackedEdgeKey tokens → PackedEdgeKey tokens
  | .scanned before after cursor =>
      PackedEdgeKey.scanned before.raw after.raw cursor
  | .completed waiting finished after shared =>
      PackedEdgeKey.completed waiting.raw finished.raw after.raw shared

/-- Raw edge validity together with the exact contextual transition. -/
def StructurallyValid
    (file : WorkspaceFile)
    (tokens : List Token)
    (key : ContextualPackedEdgeKey tokens) : Prop :=
  PackedEdgeKey.Valid file tokens key.rawProjection ∧
    match key with
    | .scanned before after _ =>
        before.context = after.context
    | .completed waiting finished after _ =>
        finished.context =
            descendContext waiting finished.raw.production ∧
          after.context = waiting.context

end ContextualPackedEdgeKey

/-- The proof-irrelevant subtype of structurally valid contextual edges. -/
abbrev StructurallyValidContextualPackedEdge
    (file : WorkspaceFile) (tokens : List Token) : Type :=
  { key : ContextualPackedEdgeKey tokens //
    ContextualPackedEdgeKey.StructurallyValid file tokens key }

/-- The physical byte selected by one chart boundary. -/
def BoundaryByte
    (file : WorkspaceFile)
    (tokens : List Token)
    (boundary : Boundary tokens)
    (byte : Nat) : Prop :=
  TokensOwnedBy file tokens ∧
    if inRange : boundary.val < tokens.length then
      byte = tokens[boundary.val].span.startByte
    else
      byte = file.content.utf8ByteSize

namespace BoundaryByte

/-- One chart boundary selects only one physical source byte. -/
theorem functional
    {file : WorkspaceFile}
    {tokens : List Token}
    {boundary : Boundary tokens}
    {left right : Nat}
    (leftAt : BoundaryByte file tokens boundary left)
    (rightAt : BoundaryByte file tokens boundary right) :
    left = right := by
  by_cases inRange : boundary.val < tokens.length
  · simp [BoundaryByte, inRange] at leftAt rightAt
    exact leftAt.2.trans rightAt.2.symm
  · simp [BoundaryByte, inRange] at leftAt rightAt
    exact leftAt.2.trans rightAt.2.symm

end BoundaryByte

/-- The exact source span covered by an ordered half-open chart interval. -/
def ConsumedSpan
    (file : WorkspaceFile)
    (tokens : List Token)
    (origin finish : Boundary tokens)
    (span : SourceSpan) : Prop :=
  TokensOwnedBy file tokens ∧
    origin.val ≤ finish.val ∧
    if occupied : origin.val < Nat.min finish.val tokens.length then
      have firstInRange : origin.val < tokens.length :=
        Nat.lt_of_lt_of_le occupied (Nat.min_le_right _ _)
      have lastInRange : Nat.min finish.val tokens.length - 1 < tokens.length := by
        have positive : 0 < Nat.min finish.val tokens.length :=
          Nat.zero_lt_of_lt occupied
        exact Nat.lt_of_lt_of_le
          (Nat.sub_lt positive Nat.zero_lt_one)
          (Nat.min_le_right _ _)
      span = {
        source := file.id
        startByte := (tokens[origin.val]'firstInRange).span.startByte
        endByte :=
          (tokens[Nat.min finish.val tokens.length - 1]'lastInRange).span.endByte
      }
    else
      ∃ byte,
        BoundaryByte file tokens origin byte ∧
          span = {
            source := file.id
            startByte := byte
            endByte := byte
          }

namespace ConsumedSpan

/-- One ordered chart interval has only one exact consumed source span. -/
theorem functional
    {file : WorkspaceFile}
    {tokens : List Token}
    {origin finish : Boundary tokens}
    {left right : SourceSpan}
    (leftConsumed : ConsumedSpan file tokens origin finish left)
    (rightConsumed : ConsumedSpan file tokens origin finish right) :
    left = right := by
  by_cases occupied : origin.val < Nat.min finish.val tokens.length
  · simp [ConsumedSpan, occupied] at leftConsumed rightConsumed
    exact leftConsumed.2.2.trans rightConsumed.2.2.symm
  · simp [ConsumedSpan, occupied] at leftConsumed rightConsumed
    rcases leftConsumed.2.2 with ⟨leftByte, leftAt, leftSpan⟩
    rcases rightConsumed.2.2 with ⟨rightByte, rightAt, rightSpan⟩
    have byteEq : leftByte = rightByte :=
      BoundaryByte.functional leftAt rightAt
    subst rightByte
    exact leftSpan.trans rightSpan.symm

end ConsumedSpan

/-- A checked source span for one completed chart interval. -/
structure ConsumedSpanWitness
    (file : WorkspaceFile)
    (tokens : List Token)
    (origin finish : Boundary tokens) where
  span : SourceSpan
  consumed : ConsumedSpan file tokens origin finish span
  deriving Repr, DecidableEq

instance {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens} :
    BEq (ConsumedSpanWitness file tokens origin finish) :=
  ⟨fun left right => decide (left = right)⟩

/-- Locate a payload with an already checked consumed-span witness. -/
def sourceLoc
    {file : WorkspaceFile}
    {tokens : List Token}
    {origin finish : Boundary tokens}
    {α : Type}
    (witness : ConsumedSpanWitness file tokens origin finish)
    (payload : α) : Located α :=
  { span := witness.span, payload := payload }

/-- A located payload uses the checked span of this completed interval. -/
def SourceLocates
    {α : Type}
    (file : WorkspaceFile)
    (tokens : List Token)
    (origin finish : Boundary tokens)
    (payload : α)
    (located : Located α) : Prop :=
  ∃ witness : ConsumedSpanWitness file tokens origin finish,
    located = sourceLoc witness payload

namespace SourceLocates

/-- A payload and completed interval determine only one located value. -/
theorem functional
    {α : Type}
    {file : WorkspaceFile}
    {tokens : List Token}
    {origin finish : Boundary tokens}
    {payload : α}
    {left right : Located α}
    (leftLocates : SourceLocates file tokens origin finish payload left)
    (rightLocates : SourceLocates file tokens origin finish payload right) :
    left = right := by
  rcases leftLocates with ⟨leftWitness, leftEq⟩
  rcases rightLocates with ⟨rightWitness, rightEq⟩
  have spanEq : leftWitness.span = rightWitness.span :=
    ConsumedSpan.functional leftWitness.consumed rightWitness.consumed
  calc
    left = sourceLoc leftWitness payload := leftEq
    _ = sourceLoc rightWitness payload := by
      simpa [sourceLoc] using
        congrArg
          (fun span => ({ span := span, payload := payload } : Located α))
          spanEq
    _ = right := rightEq.symm

end SourceLocates

namespace ConsumedSpanWitness

/-- Construct the exact consumed span for every owned, ordered chart interval. -/
def compute
    (file : WorkspaceFile)
    (tokens : List Token)
    (origin finish : Boundary tokens)
    (owned : TokensOwnedBy file tokens)
    (ordered : origin.val ≤ finish.val) :
    ConsumedSpanWitness file tokens origin finish :=
  if occupied : origin.val < Nat.min finish.val tokens.length then
    have firstInRange : origin.val < tokens.length :=
      (Nat.lt_min.mp occupied).2
    have capPositive : 0 < Nat.min finish.val tokens.length :=
      Nat.lt_of_le_of_lt (Nat.zero_le origin.val) occupied
    have lastInRange : Nat.min finish.val tokens.length - 1 < tokens.length :=
      Nat.lt_of_lt_of_le
        (Nat.sub_lt capPositive Nat.zero_lt_one)
        (Nat.min_le_right _ _)
    let span : SourceSpan := {
      source := file.id
      startByte := (tokens[origin.val]'firstInRange).span.startByte
      endByte :=
        (tokens[Nat.min finish.val tokens.length - 1]'lastInRange).span.endByte
    }
    {
      span := span
      consumed := by
        simp [ConsumedSpan, occupied, span, owned, ordered]
    }
  else
    let byte : Nat :=
      if inRange : origin.val < tokens.length then
        tokens[origin.val].span.startByte
      else
        file.content.utf8ByteSize
    have atBoundary : BoundaryByte file tokens origin byte := by
      unfold BoundaryByte byte
      refine ⟨owned, ?_⟩
      split <;> rfl
    let span : SourceSpan := {
      source := file.id
      startByte := byte
      endByte := byte
    }
    {
      span := span
      consumed := by
        refine ⟨owned, ordered, ?_⟩
        simp only [occupied, ↓reduceDIte]
        exact ⟨byte, atBoundary, rfl⟩
    }

end ConsumedSpanWitness

namespace Expected

/-- The stable finite-table index within a payload-bearing constructor. -/
private def payloadIndex : Expected → Nat
  | .hardKeyword keyword => keyword.ctorIdx
  | .contextualKeyword keyword => keyword.ctorIdx
  | .pragmaName kind => kind.ctorIdx
  | .symbol value => value.ctorIdx
  | .identifier
  | .pathComponent
  | .literal
  | .assemblyBlock
  | .endOfFile => 0

/-- Compare expectations by constructor order and then displayed finite index. -/
protected def compare (left right : Expected) : Ordering :=
  match compare left.ctorIdx right.ctorIdx with
  | .eq => compare left.payloadIndex right.payloadIndex
  | order => order

instance : Ord Expected := ⟨Expected.compare⟩

end Expected

end Solcore.Surface.Multi
