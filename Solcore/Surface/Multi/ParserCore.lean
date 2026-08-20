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

/-- Exact spelling and parsed value projected from one identifier terminal. -/
def IdentifierProjects
    {file : WorkspaceFile} {tokens : List Token}
    (terminal : MatchedTerminal file tokens (.category .identifier))
    (spelling : String) (parsed : Identifier) : Prop :=
  ∃ token : Token,
    terminal.value = .retained token ∧
      token.payload = .identifier spelling ∧
      Identifier.parse spelling = some parsed

/-- Expose the raw equations of an identifier projection. -/
theorem matchedTerminal_identifier_projection_exact
    {file : WorkspaceFile} {tokens : List Token}
    (terminal : MatchedTerminal file tokens (.category .identifier))
    (spelling : String) (parsed : Identifier) :
    IdentifierProjects terminal spelling parsed ↔
      ∃ token : Token,
        terminal.value = .retained token ∧
          token.payload = .identifier spelling ∧
          Identifier.parse spelling = some parsed :=
  Iff.rfl

/-- Exact spelling and parsed value projected from one path terminal. -/
def PathSegmentProjects
    {file : WorkspaceFile} {tokens : List Token}
    (terminal : MatchedTerminal file tokens (.category .pathComponent))
    (spelling : String) (parsed : PathSegment) : Prop :=
  ∃ token : Token,
    terminal.value = .retained token ∧
      (token.payload = .identifier spelling ∨
        ∃ keyword : HardKeyword,
          token.payload = .hardKeyword keyword ∧
            spelling = keyword.spelling) ∧
      PathSegment.parse spelling = some parsed

/-- Expose both retained-token shapes of a path projection. -/
theorem matchedTerminal_path_projection_exact
    {file : WorkspaceFile} {tokens : List Token}
    (terminal : MatchedTerminal file tokens (.category .pathComponent))
    (spelling : String) (parsed : PathSegment) :
    PathSegmentProjects terminal spelling parsed ↔
      ∃ token : Token,
        terminal.value = .retained token ∧
          (token.payload = .identifier spelling ∨
            ∃ keyword : HardKeyword,
              token.payload = .hardKeyword keyword ∧
                spelling = keyword.spelling) ∧
          PathSegment.parse spelling = some parsed :=
  Iff.rfl

/-- Exact spelling and external-library value projected from one path terminal. -/
def ExternalLibraryProjects
    {file : WorkspaceFile} {tokens : List Token}
    (terminal : MatchedTerminal file tokens (.category .pathComponent))
    (spelling : String) (parsed : ExternalLibraryName) : Prop :=
  ∃ token : Token,
    terminal.value = .retained token ∧
      (token.payload = .identifier spelling ∨
        ∃ keyword : HardKeyword,
          token.payload = .hardKeyword keyword ∧
            spelling = keyword.spelling) ∧
      ExternalLibraryName.parse spelling = some parsed

/-- Expose both retained-token shapes of an external-library projection. -/
theorem matchedTerminal_external_projection_exact
    {file : WorkspaceFile} {tokens : List Token}
    (terminal : MatchedTerminal file tokens (.category .pathComponent))
    (spelling : String) (parsed : ExternalLibraryName) :
    ExternalLibraryProjects terminal spelling parsed ↔
      ∃ token : Token,
        terminal.value = .retained token ∧
          (token.payload = .identifier spelling ∨
            ∃ keyword : HardKeyword,
              token.payload = .hardKeyword keyword ∧
                spelling = keyword.spelling) ∧
          ExternalLibraryName.parse spelling = some parsed :=
  Iff.rfl

/-- Exact spelling-preserving payload projected from one literal terminal. -/
def LiteralProjects
    {file : WorkspaceFile} {tokens : List Token}
    {terminal : TerminalSymbol}
    (matched : MatchedTerminal file tokens terminal)
    (literalPayload : LiteralPayload) : Prop :=
  ∃ token : Token,
    matched.value = .retained token ∧
      ((terminal = .category .decimalLiteral ∧
          ∃ spelling digits : String,
            token.payload = .decimalLiteral spelling digits ∧
              literalPayload = .decimal spelling digits) ∨
        (terminal = .category .hexadecimalLiteral ∧
          ∃ spelling digits : String,
            token.payload = .hexadecimalLiteral spelling digits ∧
              literalPayload = .hexadecimal spelling digits) ∨
        (terminal = .category .stringLiteral ∧
          ∃ spelling decoded : String,
            token.payload = .stringLiteral spelling decoded ∧
              literalPayload = .string spelling decoded))

/-- Expose the three exact terminal/payload branches of a literal projection. -/
theorem matchedTerminal_literal_projection_exact
    {file : WorkspaceFile} {tokens : List Token}
    {terminal : TerminalSymbol}
    (matched : MatchedTerminal file tokens terminal)
    (literalPayload : LiteralPayload) :
    LiteralProjects matched literalPayload ↔
      ∃ token : Token,
        matched.value = .retained token ∧
          ((terminal = .category .decimalLiteral ∧
              ∃ spelling digits : String,
                token.payload = .decimalLiteral spelling digits ∧
                  literalPayload = .decimal spelling digits) ∨
            (terminal = .category .hexadecimalLiteral ∧
              ∃ spelling digits : String,
                token.payload = .hexadecimalLiteral spelling digits ∧
                  literalPayload = .hexadecimal spelling digits) ∨
            (terminal = .category .stringLiteral ∧
              ∃ spelling decoded : String,
                token.payload = .stringLiteral spelling decoded ∧
                  literalPayload = .string spelling decoded)) :=
  Iff.rfl

/-- Exact opaque assembly slice projected from one assembly terminal. -/
def AssemblySliceProjects
    {file : WorkspaceFile} {tokens : List Token}
    (terminal : MatchedTerminal file tokens (.category .assemblyBlock))
    (slice : AssemblySlice) : Prop :=
  ∃ token : Token,
    terminal.value = .retained token ∧
      token.payload = .assemblyBlock slice

/-- Expose the retained token and payload equation of an assembly projection. -/
theorem matchedTerminal_assembly_projection_exact
    {file : WorkspaceFile} {tokens : List Token}
    (terminal : MatchedTerminal file tokens (.category .assemblyBlock))
    (slice : AssemblySlice) :
    AssemblySliceProjects terminal slice ↔
      ∃ token : Token,
        terminal.value = .retained token ∧
          token.payload = .assemblyBlock slice :=
  Iff.rfl

/-- The structural size of one finite EBNF expression. -/
def ebnfSize : EbnfExpr → Nat
  | .atom _ => 1
  | .sequence children => 1 + (children.map ebnfSize).sum
  | .group child => 1 + ebnfSize child
  | .choice branches => 1 + (branches.map ebnfSize).sum
  | .optional child => 1 + ebnfSize child
  | .star child => 1 + ebnfSize child
  | .plus child => 1 + ebnfSize child
  | .list0 element => 1 + ebnfSize element
  | .list1 element => 1 + ebnfSize element

/-- The six unary constructors of the EBNF expression algebra. -/
inductive UnaryEbnfKind where
  | group
  | optional
  | star
  | plus
  | list0
  | list1

namespace UnaryEbnfKind

/-- Apply one unary EBNF constructor to its child expression. -/
def apply : UnaryEbnfKind → EbnfExpr → EbnfExpr
  | .group, child => .group child
  | .optional, child => .optional child
  | .star, child => .star child
  | .plus, child => .plus child
  | .list0, child => .list0 child
  | .list1, child => .list1 child

end UnaryEbnfKind

/-- An index selecting one EBNF expression or a sequence of expressions. -/
inductive EbnfValueIndex where
  | expression (expression : EbnfExpr)
  | expressions (expressions : List EbnfExpr)

namespace EbnfValueIndex

/-- The well-founded measure of an EBNF semantic-value index. -/
def measure : EbnfValueIndex → Nat
  | .expression value => 2 * ebnfSize value
  | .expressions values => 2 * (values.map ebnfSize).sum + 1

end EbnfValueIndex

/-- Every finite EBNF expression has positive structural size. -/
theorem ebnfSize_positive (expression : EbnfExpr) :
    0 < ebnfSize expression := by
  cases expression <;> simp only [ebnfSize] <;> omega

/-- A member's size is bounded by the sum of all mapped member sizes. -/
private theorem ebnfSize_le_mapped_sum
    {expression : EbnfExpr} :
    ∀ {expressions : List EbnfExpr},
      expression ∈ expressions →
        ebnfSize expression ≤ (expressions.map ebnfSize).sum
  | [], member => by
      simp at member
  | head :: tail, member => by
      rcases List.mem_cons.mp member with equal | inTail
      · subst head
        simp only [List.map_cons, List.sum_cons]
        exact Nat.le_add_right _ _
      · simp only [List.map_cons, List.sum_cons]
        exact Nat.le_trans
          (ebnfSize_le_mapped_sum inTail)
          (Nat.le_add_left _ _)

/-- A sequence's expression-list index is strictly smaller. -/
theorem measure_sequence_lt (children : List EbnfExpr) :
    EbnfValueIndex.measure (.expressions children) <
      EbnfValueIndex.measure (.expression (.sequence children)) := by
  simp only [EbnfValueIndex.measure, ebnfSize]
  omega

/-- A selected choice branch is strictly smaller than its choice. -/
theorem measure_choice_get_lt
    (branches : List EbnfExpr)
    (branch : Fin branches.length) :
    EbnfValueIndex.measure (.expression (branches.get branch)) <
      EbnfValueIndex.measure (.expression (.choice branches)) := by
  have bound : ebnfSize (branches.get branch) ≤
      (branches.map ebnfSize).sum :=
    ebnfSize_le_mapped_sum (List.get_mem branches branch)
  simp only [EbnfValueIndex.measure, ebnfSize]
  omega

/-- A unary constructor's child index is strictly smaller. -/
theorem measure_unary_child_lt
    (kind : UnaryEbnfKind)
    (child : EbnfExpr) :
    EbnfValueIndex.measure (.expression child) <
      EbnfValueIndex.measure (.expression (kind.apply child)) := by
  cases kind <;>
    simp only [UnaryEbnfKind.apply, EbnfValueIndex.measure, ebnfSize] <;>
    omega

/-- The head expression index is strictly smaller than the whole list. -/
theorem measure_cons_head_lt
    (child : EbnfExpr)
    (rest : List EbnfExpr) :
    EbnfValueIndex.measure (.expression child) <
      EbnfValueIndex.measure (.expressions (child :: rest)) := by
  simp only [EbnfValueIndex.measure, List.map_cons, List.sum_cons]
  omega

/-- The tail expression-list index is strictly smaller than the whole list. -/
theorem measure_cons_tail_lt
    (child : EbnfExpr)
    (rest : List EbnfExpr) :
    EbnfValueIndex.measure (.expressions rest) <
      EbnfValueIndex.measure (.expressions (child :: rest)) := by
  have positive := ebnfSize_positive child
  simp only [EbnfValueIndex.measure, List.map_cons, List.sum_cons]
  omega

/-- The well-founded semantic carrier shared by expressions and expression lists. -/
def EbnfFamily
    (file : WorkspaceFile)
    (tokens : List Token) :
    (index : EbnfValueIndex) → Type
  | .expression (.atom (.terminal terminal)) =>
      MatchedTerminal file tokens terminal
  | .expression (.atom (.nonterminal rule)) =>
      RuleValue rule
  | .expression (.sequence children) =>
      EbnfFamily file tokens (.expressions children)
  | .expression (.group child) =>
      EbnfFamily file tokens (.expression child)
  | .expression (.choice branches) =>
      (branch : Fin branches.length) ×
        EbnfFamily file tokens (.expression (branches.get branch))
  | .expression (.optional child) =>
      Option (EbnfFamily file tokens (.expression child))
  | .expression (.star child) =>
      List (EbnfFamily file tokens (.expression child))
  | .expression (.plus child) =>
      NonemptyList (EbnfFamily file tokens (.expression child))
  | .expression (.list0 element) =>
      List (EbnfFamily file tokens (.expression element))
  | .expression (.list1 element) =>
      NonemptyList (EbnfFamily file tokens (.expression element))
  | .expressions [] => Unit
  | .expressions (child :: rest) =>
      EbnfFamily file tokens (.expression child) ×
        EbnfFamily file tokens (.expressions rest)
termination_by index => index.measure
decreasing_by
  · exact measure_sequence_lt children
  · exact measure_unary_child_lt .group child
  · exact measure_choice_get_lt branches branch
  · exact measure_unary_child_lt .optional child
  · exact measure_unary_child_lt .star child
  · exact measure_unary_child_lt .plus child
  · exact measure_unary_child_lt .list0 element
  · exact measure_unary_child_lt .list1 element
  · exact measure_cons_head_lt child rest
  · exact measure_cons_tail_lt child rest

/-- The semantic carrier of one EBNF expression. -/
abbrev EbnfValue
    (file : WorkspaceFile)
    (tokens : List Token)
    (expression : EbnfExpr) : Type :=
  EbnfFamily file tokens (.expression expression)

/-- The heterogeneous semantic carrier of an expression sequence. -/
abbrev EbnfValues
    (file : WorkspaceFile)
    (tokens : List Token)
    (expressions : List EbnfExpr) : Type :=
  EbnfFamily file tokens (.expressions expressions)

/-- A terminal atom carries its exact checked terminal match. -/
@[simp] theorem ebnfValue_atom_terminal_eq
    {file : WorkspaceFile}
    {tokens : List Token}
    (terminal : TerminalSymbol) :
    EbnfValue file tokens (.atom (.terminal terminal)) =
      MatchedTerminal file tokens terminal := by
  exact EbnfFamily.eq_def file tokens _

/-- A nonterminal atom carries the exact semantic value of its source rule. -/
@[simp] theorem ebnfValue_atom_nonterminal_eq
    {file : WorkspaceFile}
    {tokens : List Token}
    (rule : GrammarRuleId) :
    EbnfValue file tokens (.atom (.nonterminal rule)) =
      RuleValue rule := by
  exact EbnfFamily.eq_def file tokens _

/-- A sequence expression carries its heterogeneous child sequence. -/
@[simp] theorem ebnfValue_sequence_eq
    {file : WorkspaceFile}
    {tokens : List Token}
    (children : List EbnfExpr) :
    EbnfValue file tokens (.sequence children) =
      EbnfValues file tokens children := by
  exact EbnfFamily.eq_def file tokens _

/-- A group carries exactly its child value. -/
@[simp] theorem ebnfValue_group_eq
    {file : WorkspaceFile}
    {tokens : List Token}
    (child : EbnfExpr) :
    EbnfValue file tokens (.group child) =
      EbnfValue file tokens child := by
  exact EbnfFamily.eq_def file tokens _

/-- A choice carries its finite branch tag and that branch's exact value. -/
@[simp] theorem ebnfValue_choice_eq
    {file : WorkspaceFile}
    {tokens : List Token}
    (branches : List EbnfExpr) :
    EbnfValue file tokens (.choice branches) =
      ((branch : Fin branches.length) ×
        EbnfValue file tokens (branches.get branch)) := by
  exact EbnfFamily.eq_def file tokens _

/-- An optional expression carries an optional child value. -/
@[simp] theorem ebnfValue_optional_eq
    {file : WorkspaceFile}
    {tokens : List Token}
    (child : EbnfExpr) :
    EbnfValue file tokens (.optional child) =
      Option (EbnfValue file tokens child) := by
  exact EbnfFamily.eq_def file tokens _

/-- A star expression carries its ordered child values. -/
@[simp] theorem ebnfValue_star_eq
    {file : WorkspaceFile}
    {tokens : List Token}
    (child : EbnfExpr) :
    EbnfValue file tokens (.star child) =
      List (EbnfValue file tokens child) := by
  exact EbnfFamily.eq_def file tokens _

/-- A plus expression carries a nonempty ordered child sequence. -/
@[simp] theorem ebnfValue_plus_eq
    {file : WorkspaceFile}
    {tokens : List Token}
    (child : EbnfExpr) :
    EbnfValue file tokens (.plus child) =
      NonemptyList (EbnfValue file tokens child) := by
  exact EbnfFamily.eq_def file tokens _

/-- A possibly empty comma list carries its ordered element values. -/
@[simp] theorem ebnfValue_list0_eq
    {file : WorkspaceFile}
    {tokens : List Token}
    (element : EbnfExpr) :
    EbnfValue file tokens (.list0 element) =
      List (EbnfValue file tokens element) := by
  exact EbnfFamily.eq_def file tokens _

/-- A nonempty comma list carries its nonempty ordered element values. -/
@[simp] theorem ebnfValue_list1_eq
    {file : WorkspaceFile}
    {tokens : List Token}
    (element : EbnfExpr) :
    EbnfValue file tokens (.list1 element) =
      NonemptyList (EbnfValue file tokens element) := by
  exact EbnfFamily.eq_def file tokens _

/-- The empty expression sequence carries `Unit`. -/
@[simp] theorem ebnfValues_nil_eq
    {file : WorkspaceFile}
    {tokens : List Token} :
    EbnfValues file tokens [] = Unit := by
  exact EbnfFamily.eq_def file tokens _

/-- A nonempty expression sequence carries its head and tail values. -/
@[simp] theorem ebnfValues_cons_eq
    {file : WorkspaceFile}
    {tokens : List Token}
    (child : EbnfExpr)
    (rest : List EbnfExpr) :
    EbnfValues file tokens (child :: rest) =
      (EbnfValue file tokens child × EbnfValues file tokens rest) := by
  exact EbnfFamily.eq_def file tokens _

/-- The semantic value carried by one nonterminal symbol. -/
def NonterminalValue
    (file : WorkspaceFile)
    (tokens : List Token) : NonterminalSymbol → Type
  | .rule rule => RuleValue rule
  | .aux site => EbnfValue file tokens site.expression
  | .tail site =>
      List (EbnfValue file tokens site.element.expression)

/-- The semantic value carried by one grammar symbol. -/
def GrammarSymbolValue
    (file : WorkspaceFile)
    (tokens : List Token) : GrammarSymbol → Type
  | .terminal terminal => MatchedTerminal file tokens terminal
  | .nonterminal nonterminal =>
      NonterminalValue file tokens nonterminal

/-- A type-indexed tuple of semantic grammar-symbol values. -/
def GrammarSymbolValues
    (file : WorkspaceFile)
    (tokens : List Token) : List GrammarSymbol → Type
  | [] => Unit
  | symbol :: rest =>
      GrammarSymbolValue file tokens symbol ×
        GrammarSymbolValues file tokens rest

namespace GrammarSymbolValues

/-- Append two type-indexed grammar-symbol value tuples. -/
def append
    {file : WorkspaceFile}
    {tokens : List Token}
    {left right : List GrammarSymbol}
    (leftValues : GrammarSymbolValues file tokens left)
    (rightValues : GrammarSymbolValues file tokens right) :
    GrammarSymbolValues file tokens (left ++ right) :=
  match left with
  | [] => rightValues
  | _symbol :: _rest =>
      (leftValues.1, append leftValues.2 rightValues)

/-- Transport a grammar-symbol value tuple along an index equality. -/
def transport
    {file : WorkspaceFile}
    {tokens : List Token}
    {left right : List GrammarSymbol}
    (equality : left = right) :
    GrammarSymbolValues file tokens left →
      GrammarSymbolValues file tokens right :=
  Eq.mp (congrArg (GrammarSymbolValues file tokens) equality)

end GrammarSymbolValues

/-- Semantic values for the already consumed prefix of one item. -/
abbrev PrefixValues
    (file : WorkspaceFile)
    (tokens : List Token)
    (item : ContextualItemKey tokens) : Type :=
  GrammarSymbolValues file tokens
    (item.raw.production.rhs.take item.raw.dot.val)

namespace PrefixValues

/-- Construct the unique semantic value of a zero-length prefix. -/
def zeroValue
    {file : WorkspaceFile}
    {tokens : List Token}
    (item : ContextualItemKey tokens)
    (zero : item.raw.dot.val = 0) :
    PrefixValues file tokens item :=
  GrammarSymbolValues.transport
    (prefix_zero_layout item.raw zero) ()

/-- Append one matched terminal while scanning an item. -/
def scanValue
    {file : WorkspaceFile}
    {tokens : List Token}
    (before after : ContextualItemKey tokens)
    (terminal : TerminalSymbol)
    (next : NextSymbol before.raw (.terminal terminal))
    (matched : MatchedTerminal file tokens terminal)
    (advance : AdvanceItem before.raw
      matched.cursor.afterBoundary after.raw)
    (prior : PrefixValues file tokens before) :
    PrefixValues file tokens after :=
  GrammarSymbolValues.transport
    (prefix_scan_layout before.raw after.raw terminal
      matched.cursor.afterBoundary next advance)
    (GrammarSymbolValues.append prior (matched, ()))

/-- Append one completed nonterminal while advancing a waiting item. -/
def completeValue
    {file : WorkspaceFile}
    {tokens : List Token}
    (waiting finished after : ContextualItemKey tokens)
    (next : NextSymbol waiting.raw
      (.nonterminal finished.raw.production.lhs))
    (advance : AdvanceItem waiting.raw finished.raw.current after.raw)
    (prior : PrefixValues file tokens waiting)
    (value : NonterminalValue file tokens
      finished.raw.production.lhs) :
    PrefixValues file tokens after :=
  GrammarSymbolValues.transport
    (prefix_complete_layout waiting.raw finished.raw after.raw next advance)
    (GrammarSymbolValues.append prior (value, ()))

/-- Reindex a complete prefix as the full production right-hand side. -/
def fullValue
    {file : WorkspaceFile}
    {tokens : List Token}
    (item : ContextualItemKey tokens)
    (complete : CompleteItem item.raw)
    (prior : PrefixValues file tokens item) :
    GrammarSymbolValues file tokens item.raw.production.rhs :=
  GrammarSymbolValues.transport
    (prefix_full_layout item.raw complete) prior

end PrefixValues

namespace EbnfValue

/-- Transport one EBNF value along a checked expression equality. -/
def transport
    {file : WorkspaceFile}
    {tokens : List Token}
    {left right : EbnfExpr}
    (equality : left = right) :
    EbnfValue file tokens left → EbnfValue file tokens right :=
  Eq.mp (congrArg (EbnfValue file tokens) equality)

/-- View a site-indexed value at a checked displayed expression shape. -/
def atShape
    {file : WorkspaceFile}
    {tokens : List Token}
    {site : GrammarSite}
    {expression : EbnfExpr}
    (shape : site.expression = expression) :
    EbnfValue file tokens site.expression →
      EbnfValue file tokens expression :=
  transport shape

/-- Return a displayed expression value to its checked site index. -/
def ofShape
    {file : WorkspaceFile}
    {tokens : List Token}
    {site : GrammarSite}
    {expression : EbnfExpr}
    (shape : site.expression = expression) :
    EbnfValue file tokens expression →
      EbnfValue file tokens site.expression :=
  transport shape.symm

/-- Construct the checked EBNF value of one terminal atom. -/
def terminalAtom
    {file : WorkspaceFile}
    {tokens : List Token}
    (terminal : TerminalSymbol) :
    MatchedTerminal file tokens terminal →
      EbnfValue file tokens (EbnfExpr.atom (.terminal terminal)) :=
  Eq.mp (ebnfValue_atom_terminal_eq terminal).symm

/-- Construct the checked EBNF value of one grammar-rule atom. -/
def ruleAtom
    {file : WorkspaceFile}
    {tokens : List Token}
    (rule : GrammarRuleId) :
    RuleValue rule →
      EbnfValue file tokens (EbnfExpr.atom (.nonterminal rule)) :=
  Eq.mp (ebnfValue_atom_nonterminal_eq rule).symm

/-- Construct the checked EBNF value of one sequence. -/
def sequence
    {file : WorkspaceFile}
    {tokens : List Token}
    (children : List EbnfExpr) :
    EbnfValues file tokens children →
      EbnfValue file tokens (EbnfExpr.sequence children) :=
  Eq.mp (ebnfValue_sequence_eq children).symm

/-- Construct the checked EBNF value of one group. -/
def group
    {file : WorkspaceFile}
    {tokens : List Token}
    (child : EbnfExpr) :
    EbnfValue file tokens child →
      EbnfValue file tokens (EbnfExpr.group child) :=
  Eq.mp (ebnfValue_group_eq child).symm

/-- Construct the checked EBNF value of one tagged choice branch. -/
def choice
    {file : WorkspaceFile}
    {tokens : List Token}
    (branches : List EbnfExpr) :
    ((branch : Fin branches.length) ×
      EbnfValue file tokens (branches.get branch)) →
      EbnfValue file tokens (EbnfExpr.choice branches) :=
  Eq.mp (ebnfValue_choice_eq branches).symm

/-- Construct the checked EBNF value of one optional expression. -/
def optional
    {file : WorkspaceFile}
    {tokens : List Token}
    (child : EbnfExpr) :
    Option (EbnfValue file tokens child) →
      EbnfValue file tokens (EbnfExpr.optional child) :=
  Eq.mp (ebnfValue_optional_eq child).symm

/-- Construct the checked EBNF value of one star expression. -/
def star
    {file : WorkspaceFile}
    {tokens : List Token}
    (child : EbnfExpr) :
    List (EbnfValue file tokens child) →
      EbnfValue file tokens (EbnfExpr.star child) :=
  Eq.mp (ebnfValue_star_eq child).symm

/-- Construct the checked EBNF value of one plus expression. -/
def plus
    {file : WorkspaceFile}
    {tokens : List Token}
    (child : EbnfExpr) :
    NonemptyList (EbnfValue file tokens child) →
      EbnfValue file tokens (EbnfExpr.plus child) :=
  Eq.mp (ebnfValue_plus_eq child).symm

/-- Construct the checked EBNF value of one possibly empty comma list. -/
def list0
    {file : WorkspaceFile}
    {tokens : List Token}
    (element : EbnfExpr) :
    List (EbnfValue file tokens element) →
      EbnfValue file tokens (EbnfExpr.list0 element) :=
  Eq.mp (ebnfValue_list0_eq element).symm

/-- Construct the checked EBNF value of one nonempty comma list. -/
def list1
    {file : WorkspaceFile}
    {tokens : List Token}
    (element : EbnfExpr) :
    NonemptyList (EbnfValue file tokens element) →
      EbnfValue file tokens (EbnfExpr.list1 element) :=
  Eq.mp (ebnfValue_list1_eq element).symm

end EbnfValue

namespace GrammarSymbolValues

/-- View production values at one checked canonical right-hand side. -/
def view
    {file : WorkspaceFile}
    {tokens : List Token}
    {production : ProductionId}
    {canonicalRhs : List GrammarSymbol}
    (layout : production.rhs = canonicalRhs) :
    GrammarSymbolValues file tokens production.rhs →
      GrammarSymbolValues file tokens canonicalRhs :=
  GrammarSymbolValues.transport layout

end GrammarSymbolValues

namespace EbnfValues

/-- Convert auxiliary nonterminal values to their expression-indexed tuple. -/
def ofAuxiliaries
    {file : WorkspaceFile}
    {tokens : List Token}
    (sites : List GrammarSite) :
    GrammarSymbolValues file tokens
      (sites.map (fun site =>
        GrammarSymbol.nonterminal (.aux site))) →
      EbnfValues file tokens
        (sites.map GrammarSite.expression) :=
  match sites with
  | [] =>
      fun _values =>
        Eq.mp
          (ebnfValues_nil_eq (file := file) (tokens := tokens)).symm ()
  | site :: rest =>
      fun values =>
        Eq.mp
          (ebnfValues_cons_eq (file := file) (tokens := tokens)
            site.expression (rest.map GrammarSite.expression)).symm
          (values.1, ofAuxiliaries rest values.2)

/-- Viewing the empty auxiliary conversion yields the unique empty tuple. -/
@[simp] theorem ofAuxiliaries_nil_eq
    {file : WorkspaceFile}
    {tokens : List Token}
    (values : GrammarSymbolValues file tokens []) :
    Eq.mp (ebnfValues_nil_eq (file := file) (tokens := tokens))
      (ofAuxiliaries (file := file) (tokens := tokens) [] values) = () := by
  change cast _ (cast _ ()) = ()
  rw [cast_cast]

/-- Viewing a cons conversion preserves its head and recursive tail. -/
@[simp] theorem ofAuxiliaries_cons_eq
    {file : WorkspaceFile}
    {tokens : List Token}
    (site : GrammarSite)
    (rest : List GrammarSite)
    (head : EbnfValue file tokens site.expression)
    (tail : GrammarSymbolValues file tokens
      (rest.map (fun child =>
        GrammarSymbol.nonterminal (.aux child)))) :
    Eq.mp
        (ebnfValues_cons_eq (file := file) (tokens := tokens)
          site.expression (rest.map GrammarSite.expression))
        (ofAuxiliaries (file := file) (tokens := tokens) (site :: rest)
          (head, tail)) =
      (head, ofAuxiliaries rest tail) := by
  change cast _ (cast _ (head, ofAuxiliaries rest tail)) = _
  rw [cast_cast]
  apply cast_eq

end EbnfValues

namespace EbnfValue

/-- Viewing a value immediately after restoring its site index is identity. -/
private theorem atShape_ofShape_eq
    {file : WorkspaceFile} {tokens : List Token}
    {site : GrammarSite} {expression : EbnfExpr}
    (shape : site.expression = expression)
    (value : EbnfValue file tokens expression) :
    atShape shape (ofShape shape value) = value := by
  unfold atShape ofShape transport
  change cast _ (cast _ value) = value
  rw [cast_cast]
  apply cast_eq

end EbnfValue

namespace RootAction

/-- Extract the checked source-rule EBNF value from a root production. -/
def unpack
    {file : WorkspaceFile} {tokens : List Token}
    (rule : GrammarRuleId) :
    GrammarSymbolValues file tokens (ProductionId.root rule).rhs →
      EbnfValue file tokens (m2cV1.rhs rule) :=
  fun values =>
    EbnfValue.atShape (GrammarSite.root_expression rule)
      (GrammarSymbolValues.view (ProductionId.rhs_root rule) values).1

/-- Root unpacking views the canonical child and restores its source shape. -/
@[simp] theorem unpack_eq
    {file : WorkspaceFile} {tokens : List Token}
    (rule : GrammarRuleId)
    (values : GrammarSymbolValues file tokens
      (ProductionId.root rule).rhs) :
    unpack rule values =
      EbnfValue.atShape (GrammarSite.root_expression rule)
        (GrammarSymbolValues.view
          (ProductionId.rhs_root rule) values).1 :=
  rfl

end RootAction

namespace AtomSite

/-- Construct the checked family value of one already translated atom. -/
private def packAtom
    {file : WorkspaceFile} {tokens : List Token} :
    (atom : EbnfAtom) →
      GrammarSymbolValue file tokens atom.grammarSymbol →
      EbnfValue file tokens (.atom atom)
  | .terminal terminal, value => EbnfValue.terminalAtom terminal value
  | .nonterminal rule, value =>
      EbnfValue.ruleAtom (file := file) (tokens := tokens) rule value

/-- Atom packing commutes with transport along an atom equality. -/
private theorem transport_packAtom
    {file : WorkspaceFile} {tokens : List Token}
    {left right : EbnfAtom}
    (equality : left = right)
    (value : GrammarSymbolValue file tokens left.grammarSymbol) :
    EbnfValue.transport (congrArg EbnfExpr.atom equality)
        (packAtom left value) =
      packAtom right
        (Eq.mp
          (congrArg (GrammarSymbolValue file tokens)
            (congrArg EbnfAtom.grammarSymbol equality))
          value) := by
  cases equality
  rfl

/-- Pack one expanded atom production into its auxiliary EBNF value. -/
def pack
    {file : WorkspaceFile} {tokens : List Token}
    (site : Grammar.AtomSite) :
    GrammarSymbolValues file tokens (ProductionId.atom site).rhs →
      NonterminalValue file tokens (ProductionId.atom site).lhs :=
  fun values =>
    let atomValue :=
      Eq.mp (congrArg (GrammarSymbolValue file tokens) site.symbol_eq)
        (GrammarSymbolValues.view (ProductionId.rhs_atom site) values).1
    EbnfValue.ofShape site.expression_eq_atom
      (packAtom site.atom atomValue)

/-- View one packed atom at an explicitly checked atom index. -/
def packAtAtom
    {file : WorkspaceFile} {tokens : List Token}
    (site : Grammar.AtomSite) (atom : EbnfAtom)
    (atomEq : site.atom = atom)
    (values : GrammarSymbolValues file tokens
      (ProductionId.atom site).rhs) :
    EbnfValue file tokens (.atom atom) :=
  EbnfValue.transport (congrArg EbnfExpr.atom atomEq)
    (EbnfValue.atShape site.expression_eq_atom (pack site values))

/-- Packing a terminal atom retains its exact checked terminal match. -/
@[simp] theorem pack_terminal_eq
    {file : WorkspaceFile} {tokens : List Token}
    (site : Grammar.AtomSite) (terminal : TerminalSymbol)
    (atomEq : site.atom = .terminal terminal)
    (values : GrammarSymbolValues file tokens
      (ProductionId.atom site).rhs) :
    packAtAtom site (.terminal terminal) atomEq values =
      EbnfValue.terminalAtom terminal
        (Eq.mp
          (congrArg (GrammarSymbolValue file tokens)
            (congrArg EbnfAtom.grammarSymbol atomEq))
          (Eq.mp
            (congrArg (GrammarSymbolValue file tokens) site.symbol_eq)
            (GrammarSymbolValues.view
              (ProductionId.rhs_atom site) values).1)) := by
  let atomValue :=
    Eq.mp (congrArg (GrammarSymbolValue file tokens) site.symbol_eq)
      (GrammarSymbolValues.view (ProductionId.rhs_atom site) values).1
  unfold packAtAtom pack
  change EbnfValue.transport (congrArg EbnfExpr.atom atomEq)
    (EbnfValue.atShape site.expression_eq_atom
      (EbnfValue.ofShape site.expression_eq_atom
        (packAtom site.atom atomValue))) = _
  rw [EbnfValue.atShape_ofShape_eq, transport_packAtom atomEq]
  rfl

/-- Packing a rule atom retains its exact source-rule semantic value. -/
@[simp] theorem pack_rule_eq
    {file : WorkspaceFile} {tokens : List Token}
    (site : Grammar.AtomSite) (rule : GrammarRuleId)
    (atomEq : site.atom = .nonterminal rule)
    (values : GrammarSymbolValues file tokens
      (ProductionId.atom site).rhs) :
    packAtAtom site (.nonterminal rule) atomEq values =
      EbnfValue.ruleAtom (file := file) (tokens := tokens) rule
        (Eq.mp
          (congrArg (GrammarSymbolValue file tokens)
            (congrArg EbnfAtom.grammarSymbol atomEq))
          (Eq.mp
            (congrArg (GrammarSymbolValue file tokens) site.symbol_eq)
            (GrammarSymbolValues.view
              (ProductionId.rhs_atom site) values).1)) := by
  let atomValue :=
    Eq.mp (congrArg (GrammarSymbolValue file tokens) site.symbol_eq)
      (GrammarSymbolValues.view (ProductionId.rhs_atom site) values).1
  unfold packAtAtom pack
  change EbnfValue.transport (congrArg EbnfExpr.atom atomEq)
    (EbnfValue.atShape site.expression_eq_atom
      (EbnfValue.ofShape site.expression_eq_atom
        (packAtom site.atom atomValue))) = _
  rw [EbnfValue.atShape_ofShape_eq, transport_packAtom atomEq]
  rfl

end AtomSite

namespace SequenceSite

/-- Pack one expanded sequence into its auxiliary EBNF value. -/
def pack
    {file : WorkspaceFile} {tokens : List Token}
    (site : Grammar.SequenceSite) :
    GrammarSymbolValues file tokens (ProductionId.seq site).rhs →
      NonterminalValue file tokens (ProductionId.seq site).lhs :=
  fun values =>
    EbnfValue.ofShape site.expression_eq_sequence
      (EbnfValue.sequence (site.children.map GrammarSite.expression)
        (EbnfValues.ofAuxiliaries site.children
          (GrammarSymbolValues.view (ProductionId.rhs_seq site) values)))

/-- Sequence packing preserves every child value in displayed order. -/
@[simp] theorem pack_eq
    {file : WorkspaceFile} {tokens : List Token}
    (site : Grammar.SequenceSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.seq site).rhs) :
    EbnfValue.atShape site.expression_eq_sequence (pack site values) =
      EbnfValue.sequence (site.children.map GrammarSite.expression)
        (EbnfValues.ofAuxiliaries site.children
          (GrammarSymbolValues.view (ProductionId.rhs_seq site) values)) := by
  exact EbnfValue.atShape_ofShape_eq _ _

end SequenceSite

namespace GroupSite

/-- Pack one expanded group into its auxiliary EBNF value. -/
def pack
    {file : WorkspaceFile} {tokens : List Token}
    (site : Grammar.GroupSite) :
    GrammarSymbolValues file tokens (ProductionId.group site).rhs →
      NonterminalValue file tokens (ProductionId.group site).lhs :=
  fun values =>
    EbnfValue.ofShape site.expression_eq_group
      (EbnfValue.group site.child.expression
        (GrammarSymbolValues.view (ProductionId.rhs_group site) values).1)

/-- Group packing preserves its unique checked child value. -/
@[simp] theorem pack_eq
    {file : WorkspaceFile} {tokens : List Token}
    (site : Grammar.GroupSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.group site).rhs) :
    EbnfValue.atShape site.expression_eq_group (pack site values) =
      EbnfValue.group site.child.expression
        (GrammarSymbolValues.view
          (ProductionId.rhs_group site) values).1 := by
  exact EbnfValue.atShape_ofShape_eq _ _

end GroupSite

namespace ChoiceSite

/-- Pack one expanded choice branch into its tagged auxiliary EBNF value. -/
def pack
    {file : WorkspaceFile} {tokens : List Token}
    (site : Grammar.ChoiceSite)
    (branch : Fin site.branchCount) :
    GrammarSymbolValues file tokens
      (ProductionId.choice site branch).rhs →
      NonterminalValue file tokens
        (ProductionId.choice site branch).lhs :=
  fun values =>
    let childValue :=
      EbnfValue.transport
        ((site.branch_expression branch).trans
          (site.branch_get_toList branch).symm)
        (GrammarSymbolValues.view
          (ProductionId.rhs_choice site branch) values).1
    EbnfValue.ofShape site.expression_eq_choice
      (EbnfValue.choice site.branchExpressions.toList
        ⟨site.branchListIndex branch, childValue⟩)

/-- Choice packing preserves the exact displayed branch tag and child. -/
@[simp] theorem pack_eq
    {file : WorkspaceFile} {tokens : List Token}
    (site : Grammar.ChoiceSite)
    (branch : Fin site.branchCount)
    (values : GrammarSymbolValues file tokens
      (ProductionId.choice site branch).rhs) :
    EbnfValue.atShape site.expression_eq_choice
        (pack site branch values) =
      EbnfValue.choice site.branchExpressions.toList
        ⟨site.branchListIndex branch,
          EbnfValue.transport
            ((site.branch_expression branch).trans
              (site.branch_get_toList branch).symm)
            (GrammarSymbolValues.view
              (ProductionId.rhs_choice site branch) values).1⟩ := by
  exact EbnfValue.atShape_ofShape_eq _ _

end ChoiceSite

namespace OptionalSite

/-- Pack either expanded optional production into its auxiliary EBNF value. -/
def pack
    {file : WorkspaceFile} {tokens : List Token}
    (site : Grammar.OptionalSite) (branch : OptionalBranch) :
    GrammarSymbolValues file tokens
      (ProductionId.opt site branch).rhs →
      NonterminalValue file tokens (ProductionId.opt site branch).lhs :=
  match branch with
  | .none => fun values =>
      match GrammarSymbolValues.view
          (ProductionId.rhs_opt_none site) values with
      | () =>
          EbnfValue.ofShape site.expression_eq_optional
            (EbnfValue.optional site.child.expression none)
  | .some => fun values =>
      EbnfValue.ofShape site.expression_eq_optional
        (EbnfValue.optional site.child.expression
          (some (GrammarSymbolValues.view
            (ProductionId.rhs_opt_some site) values).1))

/-- Empty optional packing yields the checked absent value. -/
@[simp] theorem pack_none_eq
    {file : WorkspaceFile} {tokens : List Token}
    (site : Grammar.OptionalSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.opt site .none).rhs) :
    EbnfValue.atShape site.expression_eq_optional
        (pack site .none values) =
      EbnfValue.optional site.child.expression none := by
  unfold pack
  generalize viewedEq : GrammarSymbolValues.view
    (ProductionId.rhs_opt_none site) values = viewed
  cases viewed
  exact EbnfValue.atShape_ofShape_eq _ _

/-- Present optional packing preserves its unique checked child value. -/
@[simp] theorem pack_some_eq
    {file : WorkspaceFile} {tokens : List Token}
    (site : Grammar.OptionalSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.opt site .some).rhs) :
    EbnfValue.atShape site.expression_eq_optional
        (pack site .some values) =
      EbnfValue.optional site.child.expression
        (some (GrammarSymbolValues.view
          (ProductionId.rhs_opt_some site) values).1) := by
  exact EbnfValue.atShape_ofShape_eq _ _

end OptionalSite

namespace StarSite

/-- Pack either expanded star production into its auxiliary EBNF value. -/
def pack
    {file : WorkspaceFile} {tokens : List Token}
    (site : Grammar.StarSite) (branch : NilConsBranch) :
    GrammarSymbolValues file tokens
      (ProductionId.star site branch).rhs →
      NonterminalValue file tokens (ProductionId.star site branch).lhs :=
  match branch with
  | .nil => fun values =>
      match GrammarSymbolValues.view
          (ProductionId.rhs_star_nil site) values with
      | () =>
          EbnfValue.ofShape site.expression_eq_star
            (EbnfValue.star site.child.expression [])
  | .cons => fun values =>
      let viewed := GrammarSymbolValues.view
        (ProductionId.rhs_star_cons site) values
      let tailValue :=
        EbnfValue.atShape site.expression_eq_star viewed.2.1
      let tail :=
        Eq.mp (ebnfValue_star_eq site.child.expression) tailValue
      EbnfValue.ofShape site.expression_eq_star
        (EbnfValue.star site.child.expression (viewed.1 :: tail))

/-- Empty star packing yields the checked empty repetition. -/
@[simp] theorem pack_nil_eq
    {file : WorkspaceFile} {tokens : List Token}
    (site : Grammar.StarSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.star site .nil).rhs) :
    EbnfValue.atShape site.expression_eq_star
        (pack site .nil values) =
      EbnfValue.star site.child.expression [] := by
  unfold pack
  generalize viewedEq : GrammarSymbolValues.view
    (ProductionId.rhs_star_nil site) values = viewed
  cases viewed
  exact EbnfValue.atShape_ofShape_eq _ _

/-- Extending star packing prepends one child to the recursive repetition. -/
@[simp] theorem pack_cons_eq
    {file : WorkspaceFile} {tokens : List Token}
    (site : Grammar.StarSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.star site .cons).rhs) :
    EbnfValue.atShape site.expression_eq_star
        (pack site .cons values) =
      EbnfValue.star site.child.expression
        ((GrammarSymbolValues.view
            (ProductionId.rhs_star_cons site) values).1 ::
          Eq.mp (ebnfValue_star_eq site.child.expression)
            (EbnfValue.atShape site.expression_eq_star
              (GrammarSymbolValues.view
                (ProductionId.rhs_star_cons site) values).2.1)) := by
  exact EbnfValue.atShape_ofShape_eq _ _

end StarSite

namespace PlusSite

/-- Pack either expanded plus production into its auxiliary EBNF value. -/
def pack
    {file : WorkspaceFile} {tokens : List Token}
    (site : Grammar.PlusSite) (branch : OneConsBranch) :
    GrammarSymbolValues file tokens
      (ProductionId.plus site branch).rhs →
      NonterminalValue file tokens (ProductionId.plus site branch).lhs :=
  match branch with
  | .one => fun values =>
      let viewed := GrammarSymbolValues.view
        (ProductionId.rhs_plus_one site) values
      EbnfValue.ofShape site.expression_eq_plus
        (EbnfValue.plus site.child.expression {
          head := viewed.1
          tail := []
        })
  | .cons => fun values =>
      let viewed := GrammarSymbolValues.view
        (ProductionId.rhs_plus_cons site) values
      let tailValue :=
        EbnfValue.atShape site.expression_eq_plus viewed.2.1
      let tail :=
        Eq.mp (ebnfValue_plus_eq site.child.expression) tailValue
      EbnfValue.ofShape site.expression_eq_plus
        (EbnfValue.plus site.child.expression {
          head := viewed.1
          tail := tail.head :: tail.tail
        })

/-- Singleton plus packing yields one child and no remaining values. -/
@[simp] theorem pack_one_eq
    {file : WorkspaceFile} {tokens : List Token}
    (site : Grammar.PlusSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.plus site .one).rhs) :
    EbnfValue.atShape site.expression_eq_plus
        (pack site .one values) =
      EbnfValue.plus site.child.expression {
        head := (GrammarSymbolValues.view
          (ProductionId.rhs_plus_one site) values).1
        tail := []
      } := by
  exact EbnfValue.atShape_ofShape_eq _ _

/-- Extending plus packing prepends one child to the recursive nonempty value. -/
@[simp] theorem pack_cons_eq
    {file : WorkspaceFile} {tokens : List Token}
    (site : Grammar.PlusSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.plus site .cons).rhs) :
    let viewed := GrammarSymbolValues.view
      (ProductionId.rhs_plus_cons site) values
    let tail := Eq.mp (ebnfValue_plus_eq site.child.expression)
      (EbnfValue.atShape site.expression_eq_plus viewed.2.1)
    EbnfValue.atShape site.expression_eq_plus
        (pack site .cons values) =
      EbnfValue.plus site.child.expression {
        head := viewed.1
        tail := tail.head :: tail.tail
      } := by
  exact EbnfValue.atShape_ofShape_eq _ _

end PlusSite

namespace List0Site

/-- Pack either expanded zero-or-more list production into its EBNF value. -/
def pack
    {file : WorkspaceFile} {tokens : List Token}
    (site : Grammar.List0Site) (branch : NilConsBranch) :
    GrammarSymbolValues file tokens
      (ProductionId.list0 site branch).rhs →
      NonterminalValue file tokens (ProductionId.list0 site branch).lhs :=
  match branch with
  | .nil => fun values =>
      match GrammarSymbolValues.view
          (ProductionId.rhs_list0_nil site) values with
      | () =>
          EbnfValue.ofShape site.expression_eq_list0
            (EbnfValue.list0 site.element.expression [])
  | .cons => fun values =>
      let viewed := GrammarSymbolValues.view
        (ProductionId.rhs_list0_cons site) values
      let tail := Eq.mp
        (congrArg
          (fun element : GrammarSite =>
            List (EbnfValue file tokens element.expression))
          (Grammar.ListSite.element_list0 site))
        viewed.2.1
      EbnfValue.ofShape site.expression_eq_list0
        (EbnfValue.list0 site.element.expression (viewed.1 :: tail))

/-- Empty zero-or-more list packing yields the checked empty list. -/
@[simp] theorem pack_nil_eq
    {file : WorkspaceFile} {tokens : List Token}
    (site : Grammar.List0Site)
    (values : GrammarSymbolValues file tokens
      (ProductionId.list0 site .nil).rhs) :
    EbnfValue.atShape site.expression_eq_list0
        (pack site .nil values) =
      EbnfValue.list0 site.element.expression [] := by
  unfold pack
  generalize viewedEq : GrammarSymbolValues.view
    (ProductionId.rhs_list0_nil site) values = viewed
  cases viewed
  exact EbnfValue.atShape_ofShape_eq _ _

/-- Extending zero-or-more list packing prepends its exact element. -/
@[simp] theorem pack_cons_eq
    {file : WorkspaceFile} {tokens : List Token}
    (site : Grammar.List0Site)
    (values : GrammarSymbolValues file tokens
      (ProductionId.list0 site .cons).rhs) :
    let viewed := GrammarSymbolValues.view
      (ProductionId.rhs_list0_cons site) values
    let tail := Eq.mp
      (congrArg
        (fun element : GrammarSite =>
          List (EbnfValue file tokens element.expression))
        (Grammar.ListSite.element_list0 site))
      viewed.2.1
    EbnfValue.atShape site.expression_eq_list0
        (pack site .cons values) =
      EbnfValue.list0 site.element.expression (viewed.1 :: tail) := by
  exact EbnfValue.atShape_ofShape_eq _ _

end List0Site

namespace List1Site

/-- Pack one expanded nonempty list production into its EBNF value. -/
def pack
    {file : WorkspaceFile} {tokens : List Token}
    (site : Grammar.List1Site) :
    GrammarSymbolValues file tokens (ProductionId.list1 site).rhs →
      NonterminalValue file tokens (ProductionId.list1 site).lhs :=
  fun values =>
    let viewed := GrammarSymbolValues.view
      (ProductionId.rhs_list1 site) values
    let tail := Eq.mp
      (congrArg
        (fun element : GrammarSite =>
          List (EbnfValue file tokens element.expression))
        (Grammar.ListSite.element_list1 site))
      viewed.2.1
    EbnfValue.ofShape site.expression_eq_list1
      (EbnfValue.list1 site.element.expression {
        head := viewed.1
        tail := tail
      })

/-- Nonempty list packing preserves its head and exact comma-tail values. -/
@[simp] theorem pack_eq
    {file : WorkspaceFile} {tokens : List Token}
    (site : Grammar.List1Site)
    (values : GrammarSymbolValues file tokens
      (ProductionId.list1 site).rhs) :
    let viewed := GrammarSymbolValues.view
      (ProductionId.rhs_list1 site) values
    let tail := Eq.mp
      (congrArg
        (fun element : GrammarSite =>
          List (EbnfValue file tokens element.expression))
        (Grammar.ListSite.element_list1 site))
      viewed.2.1
    EbnfValue.atShape site.expression_eq_list1 (pack site values) =
      EbnfValue.list1 site.element.expression {
        head := viewed.1
        tail := tail
      } := by
  exact EbnfValue.atShape_ofShape_eq _ _

end List1Site

namespace ListSite

/-- Pack either expanded comma-tail production into its exact element list. -/
def pack
    {file : WorkspaceFile} {tokens : List Token}
    (site : Grammar.ListSite) (branch : NilConsBranch) :
    GrammarSymbolValues file tokens
      (ProductionId.tail site branch).rhs →
      NonterminalValue file tokens (ProductionId.tail site branch).lhs :=
  match branch with
  | .nil => fun values =>
      match GrammarSymbolValues.view
          (ProductionId.rhs_tail_nil site) values with
      | () => []
  | .cons => fun values =>
      let viewed := GrammarSymbolValues.view
        (ProductionId.rhs_tail_cons site) values
      viewed.2.1 :: viewed.2.2.1

/-- Empty comma-tail packing consumes its empty RHS and returns no values. -/
@[simp] theorem pack_nil_eq
    {file : WorkspaceFile} {tokens : List Token}
    (site : Grammar.ListSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.tail site .nil).rhs) :
    pack site .nil values = [] := by
  unfold pack
  generalize viewedEq : GrammarSymbolValues.view
    (ProductionId.rhs_tail_nil site) values = viewed
  cases viewed
  rfl

/-- Extending comma-tail packing consumes its comma and prepends its element. -/
@[simp] theorem pack_cons_eq
    {file : WorkspaceFile} {tokens : List Token}
    (site : Grammar.ListSite)
    (values : GrammarSymbolValues file tokens
      (ProductionId.tail site .cons).rhs) :
    pack site .cons values =
      (GrammarSymbolValues.view
          (ProductionId.rhs_tail_cons site) values).2.1 ::
        (GrammarSymbolValues.view
          (ProductionId.rhs_tail_cons site) values).2.2.1 :=
  rfl

end ListSite

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
