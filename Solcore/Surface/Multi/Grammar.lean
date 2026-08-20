import Solcore.Surface.Multi.Diagnostic

set_option autoImplicit false

namespace Solcore.Surface.Multi.Grammar

/-- The seventy-five source nonterminals of the m2c-v1 grammar. -/
inductive GrammarRuleId where
  | «module»
  | topItem
  | moduleRef
  | importDecl
  | importEntry
  | hidingClause
  | exportDecl
  | localExportEntry
  | remoteExportEntry
  | exportItem
  | constructorSelection
  | pragmaDecl
  | genericPrefix
  | forallClause
  | forallBinder
  | optionalComma
  | predicateList
  | predicate
  | functionSignature
  | functionDecl
  | classMethod
  | dataDecl
  | dataConstructor
  | typeAliasDecl
  | classDecl
  | instanceDecl
  | instanceMethod
  | contractDecl
  | contractMember
  | fieldDecl
  | fallbackDecl
  | contractConstructorDecl
  | parameter
  | body
  | «type»
  | typeAtom
  | qualifiedName
  | statement
  | letStatement
  | letBinding
  | returnStatement
  | blockStatement
  | breakStatement
  | continueStatement
  | assemblyStatement
  | ifStatement
  | forStatement
  | forInitItem
  | forPostItem
  | matchStatement
  | matchArm
  | armStatement
  | assignmentStatement
  | assignmentOperator
  | expressionStatement
  | terminalExpression
  | pattern
  | expression
  | annotation
  | conditional
  | logicalOr
  | logicalAnd
  | equality
  | relational
  | bitOr
  | bitXor
  | bitAnd
  | additive
  | multiplicative
  | prefix
  | postfix
  | postfixPart
  | atom
  | lambda
  | literal
  deriving Repr, BEq, DecidableEq

/-- The source-rule order fixed by ADR-0015. -/
def allGrammarRuleIds : List GrammarRuleId := [
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

namespace GrammarRuleId

/-- The stable zero-based index in the displayed source-rule order. -/
def index (rule : GrammarRuleId) : Nat :=
  allGrammarRuleIds.findIdx (· == rule)

/-- Compare source rules by their displayed finite-table indices. -/
protected def compare
    (left right : GrammarRuleId) : Ordering :=
  compare left.index right.index

instance : Ord GrammarRuleId := ⟨GrammarRuleId.compare⟩

end GrammarRuleId

/-- The token payload categories referenced without a fixed spelling. -/
inductive TerminalCategory where
  | identifier
  | pathComponent
  | decimalLiteral
  | hexadecimalLiteral
  | stringLiteral
  | assemblyBlock
  deriving Repr, BEq, DecidableEq

/-- One exact terminal class of the source grammar. -/
inductive TerminalSymbol where
  | hardKeyword (keyword : HardKeyword)
  | contextualKeyword (keyword : ContextualKeyword)
  | pragmaName (kind : PragmaKind)
  | symbol (symbol : Symbol)
  | category (category : TerminalCategory)
  | endOfFile
  deriving Repr, BEq, DecidableEq

namespace TerminalCategory

/-- The diagnostic expectation shared by every spelling in this category. -/
def expected : TerminalCategory → Expected
  | .identifier => .identifier
  | .pathComponent => .pathComponent
  | .decimalLiteral
  | .hexadecimalLiteral
  | .stringLiteral => .literal
  | .assemblyBlock => .assemblyBlock

end TerminalCategory

namespace TerminalSymbol

/-- The exact frontier-diagnostic class of a grammar terminal. -/
def expected : TerminalSymbol → Expected
  | .hardKeyword keyword => .hardKeyword keyword
  | .contextualKeyword keyword => .contextualKeyword keyword
  | .pragmaName kind => .pragmaName kind
  | .symbol value => .symbol value
  | .category terminalCategory => TerminalCategory.expected terminalCategory
  | .endOfFile => .endOfFile

end TerminalSymbol

/-- A terminal or source nonterminal atom in an EBNF right-hand side. -/
inductive EbnfAtom where
  | terminal (terminal : TerminalSymbol)
  | nonterminal (rule : GrammarRuleId)
  deriving Repr, BEq, DecidableEq

/-- The exact variadic EBNF node algebra used by the source grammar. -/
inductive EbnfExpr where
  | atom (atom : EbnfAtom)
  | sequence (children : List EbnfExpr)
  | group (child : EbnfExpr)
  | choice (branches : List EbnfExpr)
  | optional (child : EbnfExpr)
  | star (child : EbnfExpr)
  | plus (child : EbnfExpr)
  | list0 (element : EbnfExpr)
  | list1 (element : EbnfExpr)
  deriving Repr, BEq

/-- One closed EBNF right-hand side for every source rule. -/
structure EbnfGrammar where
  rhs : GrammarRuleId → EbnfExpr

private def terminal (value : TerminalSymbol) : EbnfExpr :=
  .atom (.terminal value)

private def hardKeyword (keyword : HardKeyword) : EbnfExpr :=
  terminal (.hardKeyword keyword)

private def contextualKeyword (keyword : ContextualKeyword) : EbnfExpr :=
  terminal (.contextualKeyword keyword)

private def pragmaName (kind : PragmaKind) : EbnfExpr :=
  terminal (.pragmaName kind)

private def symbol (value : Symbol) : EbnfExpr :=
  terminal (.symbol value)

private def category (value : TerminalCategory) : EbnfExpr :=
  terminal (.category value)

private def nonterminal (rule : GrammarRuleId) : EbnfExpr :=
  .atom (.nonterminal rule)

private def sequence (children : List EbnfExpr) : EbnfExpr :=
  .sequence children

private def choice (branches : List EbnfExpr) : EbnfExpr :=
  .choice branches

private def group (child : EbnfExpr) : EbnfExpr :=
  .group child

private def optional (child : EbnfExpr) : EbnfExpr :=
  .optional child

private def star (child : EbnfExpr) : EbnfExpr :=
  .star child

private def plus (child : EbnfExpr) : EbnfExpr :=
  .plus child

private def list0 (element : EbnfExpr) : EbnfExpr :=
  .list0 element

private def list1 (element : EbnfExpr) : EbnfExpr :=
  .list1 element

private def identifier : EbnfExpr :=
  category .identifier

private def pathComponent : EbnfExpr :=
  category .pathComponent

private def m2cV1Rhs : GrammarRuleId → EbnfExpr
  | .module =>
      sequence [star (nonterminal .topItem), terminal .endOfFile]
  | .topItem =>
      choice [
        nonterminal .importDecl,
        nonterminal .exportDecl,
        nonterminal .pragmaDecl,
        nonterminal .dataDecl,
        nonterminal .typeAliasDecl,
        nonterminal .classDecl,
        nonterminal .instanceDecl,
        nonterminal .contractDecl,
        nonterminal .functionDecl
      ]
  | .moduleRef =>
      choice [
        sequence [
          symbol .at,
          pathComponent,
          symbol .dot,
          pathComponent,
          star (group (sequence [symbol .dot, pathComponent]))
        ],
        sequence [
          pathComponent,
          star (group (sequence [symbol .dot, pathComponent]))
        ]
      ]
  | .importDecl =>
      choice [
        sequence [
          hardKeyword .importKw,
          nonterminal .moduleRef,
          symbol .semicolon
        ],
        sequence [
          hardKeyword .importKw,
          nonterminal .moduleRef,
          hardKeyword .asKw,
          identifier,
          symbol .semicolon
        ],
        sequence [
          hardKeyword .importKw,
          nonterminal .moduleRef,
          symbol .dot,
          symbol .leftBrace,
          list0 (nonterminal .importEntry),
          symbol .rightBrace,
          optional (nonterminal .hidingClause),
          symbol .semicolon
        ]
      ]
  | .importEntry =>
      choice [
        symbol .star,
        sequence [
          identifier,
          optional (sequence [hardKeyword .asKw, identifier])
        ]
      ]
  | .hidingClause =>
      sequence [
        hardKeyword .hidingKw,
        symbol .leftBrace,
        list0 identifier,
        symbol .rightBrace
      ]
  | .exportDecl =>
      choice [
        sequence [
          hardKeyword .exportKw,
          symbol .leftBrace,
          list0 (nonterminal .localExportEntry),
          symbol .rightBrace,
          symbol .semicolon
        ],
        sequence [
          hardKeyword .exportKw,
          nonterminal .moduleRef,
          symbol .semicolon
        ],
        sequence [
          hardKeyword .exportKw,
          nonterminal .moduleRef,
          hardKeyword .asKw,
          identifier,
          symbol .semicolon
        ],
        sequence [
          hardKeyword .exportKw,
          nonterminal .moduleRef,
          symbol .dot,
          symbol .star,
          symbol .semicolon
        ],
        sequence [
          hardKeyword .exportKw,
          nonterminal .moduleRef,
          symbol .dot,
          symbol .leftBrace,
          list0 (nonterminal .remoteExportEntry),
          symbol .rightBrace,
          symbol .semicolon
        ]
      ]
  | .localExportEntry =>
      choice [
        symbol .star,
        nonterminal .exportItem,
        sequence [nonterminal .moduleRef, symbol .dot, symbol .star]
      ]
  | .remoteExportEntry =>
      choice [symbol .star, nonterminal .exportItem]
  | .exportItem =>
      sequence [identifier, optional (nonterminal .constructorSelection)]
  | .constructorSelection =>
      choice [
        sequence [symbol .leftParen, symbol .star, symbol .rightParen],
        sequence [symbol .leftParen, list1 identifier, symbol .rightParen]
      ]
  | .pragmaDecl =>
      choice [
        sequence [
          hardKeyword .pragmaKw,
          pragmaName .noCoverageCondition,
          optional (list1 identifier),
          symbol .semicolon
        ],
        sequence [
          hardKeyword .pragmaKw,
          pragmaName .noPattersonCondition,
          optional (list1 identifier),
          symbol .semicolon
        ],
        sequence [
          hardKeyword .pragmaKw,
          pragmaName .noBoundedVariableCondition,
          optional (list1 identifier),
          symbol .semicolon
        ],
        sequence [
          hardKeyword .pragmaKw,
          pragmaName .noGenericInstanceFor,
          optional (list1 identifier),
          symbol .semicolon
        ]
      ]
  | .genericPrefix =>
      sequence [
        nonterminal .forallClause,
        optional (sequence [
          nonterminal .predicateList,
          symbol .fatArrow
        ])
      ]
  | .forallClause =>
      sequence [
        hardKeyword .forallKw,
        nonterminal .forallBinder,
        star (group (sequence [
          nonterminal .optionalComma,
          nonterminal .forallBinder
        ])),
        symbol .dot
      ]
  | .forallBinder =>
      choice [
        identifier,
        sequence [
          identifier,
          symbol .colon,
          nonterminal .qualifiedName,
          optional (sequence [
            symbol .leftParen,
            list1 (nonterminal .type),
            symbol .rightParen
          ])
        ]
      ]
  | .optionalComma =>
      optional (symbol .comma)
  | .predicateList =>
      list1 (nonterminal .predicate)
  | .predicate =>
      sequence [
        nonterminal .typeAtom,
        symbol .colon,
        nonterminal .qualifiedName,
        optional (sequence [
          symbol .leftParen,
          list1 (nonterminal .type),
          symbol .rightParen
        ])
      ]
  | .functionSignature =>
      sequence [
        optional (nonterminal .genericPrefix),
        optional (hardKeyword .publicKw),
        optional (hardKeyword .payableKw),
        hardKeyword .functionKw,
        identifier,
        symbol .leftParen,
        list0 (nonterminal .parameter),
        symbol .rightParen,
        optional (sequence [symbol .arrow, nonterminal .type])
      ]
  | .functionDecl =>
      sequence [nonterminal .functionSignature, nonterminal .body]
  | .classMethod =>
      sequence [nonterminal .functionSignature, symbol .semicolon]
  | .dataDecl =>
      sequence [
        hardKeyword .dataKw,
        identifier,
        optional (sequence [
          symbol .leftParen,
          list1 identifier,
          symbol .rightParen
        ]),
        optional (sequence [
          symbol .equal,
          nonterminal .dataConstructor,
          star (group (sequence [
            symbol .pipe,
            nonterminal .dataConstructor
          ]))
        ]),
        symbol .semicolon
      ]
  | .dataConstructor =>
      sequence [
        identifier,
        optional (sequence [
          symbol .leftParen,
          list1 (nonterminal .type),
          symbol .rightParen
        ])
      ]
  | .typeAliasDecl =>
      sequence [
        hardKeyword .typeKw,
        identifier,
        optional (sequence [
          symbol .leftParen,
          list1 identifier,
          symbol .rightParen
        ]),
        symbol .equal,
        nonterminal .type,
        symbol .semicolon
      ]
  | .classDecl =>
      sequence [
        optional (nonterminal .genericPrefix),
        hardKeyword .classKw,
        nonterminal .typeAtom,
        symbol .colon,
        identifier,
        optional (sequence [
          symbol .leftParen,
          list1 (nonterminal .type),
          symbol .rightParen
        ]),
        symbol .leftBrace,
        star (nonterminal .classMethod),
        symbol .rightBrace
      ]
  | .instanceDecl =>
      sequence [
        optional (nonterminal .genericPrefix),
        optional (hardKeyword .defaultKw),
        hardKeyword .instanceKw,
        nonterminal .typeAtom,
        symbol .colon,
        nonterminal .qualifiedName,
        optional (sequence [
          symbol .leftParen,
          list1 (nonterminal .type),
          symbol .rightParen
        ]),
        symbol .leftBrace,
        star (nonterminal .instanceMethod),
        symbol .rightBrace
      ]
  | .instanceMethod =>
      nonterminal .functionDecl
  | .contractDecl =>
      sequence [
        hardKeyword .contractKw,
        identifier,
        optional (sequence [
          symbol .leftParen,
          list1 identifier,
          symbol .rightParen
        ]),
        symbol .leftBrace,
        star (nonterminal .contractMember),
        symbol .rightBrace
      ]
  | .contractMember =>
      choice [
        nonterminal .dataDecl,
        nonterminal .typeAliasDecl,
        nonterminal .fieldDecl,
        nonterminal .functionDecl,
        nonterminal .fallbackDecl,
        nonterminal .contractConstructorDecl
      ]
  | .fieldDecl =>
      sequence [
        identifier,
        symbol .colon,
        nonterminal .type,
        optional (sequence [symbol .equal, nonterminal .expression]),
        symbol .semicolon
      ]
  | .fallbackDecl =>
      sequence [
        optional (nonterminal .genericPrefix),
        optional (hardKeyword .publicKw),
        optional (hardKeyword .payableKw),
        hardKeyword .fallbackKw,
        symbol .leftParen,
        list0 (nonterminal .parameter),
        symbol .rightParen,
        optional (sequence [symbol .arrow, nonterminal .type]),
        nonterminal .body
      ]
  | .contractConstructorDecl =>
      sequence [
        optional (hardKeyword .publicKw),
        optional (hardKeyword .payableKw),
        hardKeyword .constructorKw,
        symbol .leftParen,
        list0 (nonterminal .parameter),
        symbol .rightParen,
        nonterminal .body
      ]
  | .parameter =>
      sequence [
        optional (contextualKeyword .comptimeKw),
        identifier,
        optional (sequence [symbol .colon, nonterminal .type])
      ]
  | .body =>
      sequence [
        symbol .leftBrace,
        star (nonterminal .statement),
        symbol .rightBrace
      ]
  | .type =>
      choice [
        sequence [contextualKeyword .comptimeKw, nonterminal .type],
        sequence [
          nonterminal .typeAtom,
          optional (sequence [symbol .arrow, nonterminal .type])
        ]
      ]
  | .typeAtom =>
      choice [
        sequence [symbol .at, nonterminal .typeAtom],
        sequence [
          nonterminal .qualifiedName,
          optional (sequence [
            symbol .leftParen,
            list1 (nonterminal .type),
            symbol .rightParen
          ])
        ],
        sequence [symbol .leftParen, symbol .rightParen],
        sequence [
          symbol .leftParen,
          nonterminal .type,
          symbol .rightParen
        ],
        sequence [
          symbol .leftParen,
          nonterminal .type,
          symbol .comma,
          nonterminal .type,
          star (group (sequence [symbol .comma, nonterminal .type])),
          symbol .rightParen
        ]
      ]
  | .qualifiedName =>
      sequence [
        identifier,
        star (group (sequence [symbol .dot, identifier]))
      ]
  | .statement =>
      choice [
        nonterminal .letStatement,
        nonterminal .returnStatement,
        nonterminal .matchStatement,
        nonterminal .ifStatement,
        nonterminal .forStatement,
        nonterminal .assemblyStatement,
        nonterminal .blockStatement,
        nonterminal .breakStatement,
        nonterminal .continueStatement,
        nonterminal .assignmentStatement,
        nonterminal .expressionStatement
      ]
  | .letStatement =>
      sequence [nonterminal .letBinding, symbol .semicolon]
  | .letBinding =>
      sequence [
        hardKeyword .letKw,
        identifier,
        optional (sequence [
          symbol .colon,
          optional (contextualKeyword .comptimeKw),
          nonterminal .type
        ]),
        optional (sequence [symbol .equal, nonterminal .expression])
      ]
  | .returnStatement =>
      sequence [
        hardKeyword .returnKw,
        optional (nonterminal .expression),
        symbol .semicolon
      ]
  | .blockStatement =>
      nonterminal .body
  | .breakStatement =>
      sequence [hardKeyword .breakKw, symbol .semicolon]
  | .continueStatement =>
      sequence [hardKeyword .continueKw, symbol .semicolon]
  | .assemblyStatement =>
      sequence [
        hardKeyword .assemblyKw,
        category .assemblyBlock
      ]
  | .ifStatement =>
      sequence [
        hardKeyword .ifKw,
        symbol .leftParen,
        nonterminal .expression,
        symbol .rightParen,
        nonterminal .body,
        optional (sequence [hardKeyword .elseKw, nonterminal .body])
      ]
  | .forStatement =>
      sequence [
        hardKeyword .forKw,
        symbol .leftParen,
        list0 (nonterminal .forInitItem),
        symbol .semicolon,
        nonterminal .expression,
        symbol .semicolon,
        list0 (nonterminal .forPostItem),
        symbol .rightParen,
        nonterminal .body
      ]
  | .forInitItem =>
      choice [
        nonterminal .letBinding,
        sequence [
          nonterminal .expression,
          nonterminal .assignmentOperator,
          nonterminal .expression
        ],
        nonterminal .expression
      ]
  | .forPostItem =>
      choice [
        sequence [
          nonterminal .expression,
          nonterminal .assignmentOperator,
          nonterminal .expression
        ],
        nonterminal .expression
      ]
  | .matchStatement =>
      sequence [
        hardKeyword .matchKw,
        list1 (nonterminal .expression),
        symbol .leftBrace,
        plus (nonterminal .matchArm),
        symbol .rightBrace,
        optional (symbol .semicolon)
      ]
  | .matchArm =>
      sequence [
        symbol .pipe,
        list1 (nonterminal .pattern),
        symbol .fatArrow,
        star (nonterminal .armStatement)
      ]
  | .armStatement =>
      nonterminal .statement
  | .assignmentStatement =>
      sequence [
        nonterminal .expression,
        nonterminal .assignmentOperator,
        nonterminal .expression,
        symbol .semicolon
      ]
  | .assignmentOperator =>
      choice [
        symbol .equal,
        symbol .plusEqual,
        symbol .minusEqual,
        symbol .caretEqual,
        symbol .ampEqual,
        symbol .pipeEqual,
        symbol .percentEqual
      ]
  | .expressionStatement =>
      choice [
        sequence [nonterminal .expression, symbol .semicolon],
        nonterminal .terminalExpression
      ]
  | .terminalExpression =>
      nonterminal .expression
  | .pattern =>
      choice [
        symbol .underscore,
        nonterminal .literal,
        sequence [
          symbol .dot,
          identifier,
          optional (sequence [
            symbol .leftParen,
            list1 (nonterminal .pattern),
            symbol .rightParen
          ])
        ],
        sequence [
          contextualKeyword .comptimeKw,
          nonterminal .expression
        ],
        sequence [
          nonterminal .qualifiedName,
          optional (sequence [
            symbol .leftParen,
            list1 (nonterminal .pattern),
            symbol .rightParen
          ])
        ],
        sequence [symbol .leftParen, symbol .rightParen],
        sequence [
          symbol .leftParen,
          nonterminal .pattern,
          symbol .rightParen
        ],
        sequence [
          symbol .leftParen,
          nonterminal .pattern,
          symbol .comma,
          nonterminal .pattern,
          star (group (sequence [symbol .comma, nonterminal .pattern])),
          symbol .rightParen
        ]
      ]
  | .expression =>
      nonterminal .annotation
  | .annotation =>
      sequence [
        nonterminal .conditional,
        optional (sequence [symbol .colon, nonterminal .type])
      ]
  | .conditional =>
      choice [
        sequence [
          hardKeyword .ifKw,
          nonterminal .conditional,
          contextualKeyword .thenKw,
          nonterminal .conditional,
          hardKeyword .elseKw,
          nonterminal .conditional
        ],
        sequence [
          nonterminal .logicalOr,
          optional (sequence [
            symbol .question,
            nonterminal .conditional,
            symbol .colon,
            nonterminal .conditional
          ])
        ]
      ]
  | .logicalOr =>
      sequence [
        nonterminal .logicalAnd,
        star (group (sequence [
          symbol .logicalOr,
          nonterminal .logicalAnd
        ]))
      ]
  | .logicalAnd =>
      sequence [
        nonterminal .equality,
        star (group (sequence [
          symbol .logicalAnd,
          nonterminal .equality
        ]))
      ]
  | .equality =>
      sequence [
        nonterminal .relational,
        optional (sequence [
          group (choice [symbol .equalEqual, symbol .notEqual]),
          nonterminal .relational
        ])
      ]
  | .relational =>
      sequence [
        nonterminal .bitOr,
        optional (sequence [
          group (choice [
            symbol .less,
            symbol .greater,
            symbol .lessEqual,
            symbol .greaterEqual
          ]),
          nonterminal .bitOr
        ])
      ]
  | .bitOr =>
      sequence [
        nonterminal .bitXor,
        star (group (sequence [symbol .pipe, nonterminal .bitXor]))
      ]
  | .bitXor =>
      sequence [
        nonterminal .bitAnd,
        star (group (sequence [symbol .caret, nonterminal .bitAnd]))
      ]
  | .bitAnd =>
      sequence [
        nonterminal .additive,
        star (group (sequence [symbol .amp, nonterminal .additive]))
      ]
  | .additive =>
      sequence [
        nonterminal .multiplicative,
        star (group (sequence [
          group (choice [symbol .plus, symbol .minus]),
          nonterminal .multiplicative
        ]))
      ]
  | .multiplicative =>
      sequence [
        nonterminal .prefix,
        star (group (sequence [
          group (choice [symbol .star, symbol .slash, symbol .percent]),
          nonterminal .prefix
        ]))
      ]
  | .prefix =>
      choice [
        sequence [symbol .bang, nonterminal .prefix],
        nonterminal .postfix
      ]
  | .postfix =>
      sequence [
        nonterminal .atom,
        star (nonterminal .postfixPart)
      ]
  | .postfixPart =>
      choice [
        sequence [
          symbol .leftParen,
          list0 (nonterminal .expression),
          symbol .rightParen
        ],
        sequence [symbol .dot, identifier],
        sequence [
          symbol .leftBracket,
          nonterminal .expression,
          symbol .rightBracket
        ]
      ]
  | .atom =>
      choice [
        nonterminal .literal,
        identifier,
        sequence [
          symbol .dot,
          identifier,
          optional (sequence [
            symbol .leftParen,
            list0 (nonterminal .expression),
            symbol .rightParen
          ])
        ],
        sequence [symbol .at, nonterminal .typeAtom],
        nonterminal .lambda,
        sequence [symbol .leftParen, symbol .rightParen],
        sequence [
          symbol .leftParen,
          nonterminal .expression,
          symbol .rightParen
        ],
        sequence [
          symbol .leftParen,
          nonterminal .expression,
          symbol .comma,
          nonterminal .expression,
          star (group (sequence [symbol .comma, nonterminal .expression])),
          symbol .rightParen
        ]
      ]
  | .lambda =>
      sequence [
        hardKeyword .lamKw,
        symbol .leftParen,
        list0 (nonterminal .parameter),
        symbol .rightParen,
        optional (sequence [symbol .arrow, nonterminal .type]),
        nonterminal .body
      ]
  | .literal =>
      choice [
        category .decimalLiteral,
        category .hexadecimalLiteral,
        category .stringLiteral
      ]

/-- The complete checked source EBNF for m2c-v1. -/
def m2cV1 : EbnfGrammar :=
  ⟨m2cV1Rhs⟩

namespace EbnfExpr

/-- The direct EBNF children in displayed order. -/
def children : EbnfExpr → List EbnfExpr
  | .atom _ => []
  | .sequence children => children
  | .group child
  | .optional child
  | .star child
  | .plus child
  | .list0 child
  | .list1 child => [child]
  | .choice branches => branches

/-- Resolve one root-to-node child-index path. -/
def nodeAt? (root : EbnfExpr) : List Nat → Option EbnfExpr
  | [] => some root
  | index :: rest =>
      match root.children[index]? with
      | some child => child.nodeAt? rest
      | none => none
termination_by path => path.length

mutual

private def paths : EbnfExpr → List (List Nat)
  | .atom _ => [[]]
  | .sequence children
  | .choice children =>
      [] :: indexedChildPaths 0 children
  | .group child
  | .optional child
  | .star child
  | .plus child
  | .list0 child
  | .list1 child =>
      [] :: (paths child).map (0 :: ·)

private def indexedChildPaths : Nat → List EbnfExpr → List (List Nat)
  | _, [] => []
  | index, child :: rest =>
      (paths child).map (index :: ·) ++
        indexedChildPaths (index + 1) rest

end

/-- Every valid site path in lexicographic child-index order. -/
def sitePaths (expression : EbnfExpr) : List (List Nat) :=
  expression.paths

end EbnfExpr

/-- The proof-free key of one source-grammar site. -/
structure GrammarSiteKey where
  rule : GrammarRuleId
  path : List Nat
  deriving Repr, BEq, DecidableEq

namespace GrammarSiteKey

/-- Check that the path selects an actual node of the fixed grammar. -/
def valid (key : GrammarSiteKey) : Bool :=
  ((m2cV1.rhs key.rule).nodeAt? key.path).isSome

end GrammarSiteKey

/-- A site whose child-index path is checked against `m2cV1`. -/
abbrev GrammarSite := { key : GrammarSiteKey // key.valid = true }

namespace GrammarSite

/-- Check and construct one grammar site. -/
def ofKey? (key : GrammarSiteKey) : Option GrammarSite :=
  if valid : key.valid = true then
    some ⟨key, valid⟩
  else
    none

/-- The rule-root site. -/
def root (rule : GrammarRuleId) : GrammarSite :=
  ⟨{ rule, path := [] }, by
    simp [GrammarSiteKey.valid, EbnfExpr.nodeAt?]⟩

/-- The selected EBNF node. -/
def expression (site : GrammarSite) : EbnfExpr :=
  ((m2cV1.rhs site.val.rule).nodeAt? site.val.path).get site.property

/-- Select a direct child site when the child index exists. -/
def child? (site : GrammarSite) (index : Nat) : Option GrammarSite :=
  GrammarSite.ofKey? {
    rule := site.val.rule
    path := site.val.path ++ [index]
  }

/-- The root site selects exactly the source rule right-hand side. -/
theorem root_expression (rule : GrammarRuleId) :
    (root rule).expression = m2cV1.rhs rule := by
  simp [root, expression, EbnfExpr.nodeAt?]

end GrammarSite

namespace EbnfExpr

private theorem nodeAt?_append
    (root : EbnfExpr) (path suffix : List Nat) :
    root.nodeAt? (path ++ suffix) =
      (root.nodeAt? path).bind fun selected => selected.nodeAt? suffix := by
  induction path generalizing root with
  | nil => simp [nodeAt?]
  | cons index path induction =>
      simp only [List.cons_append, nodeAt?]
      cases selected : root.children[index]? with
      | none => rfl
      | some child => exact induction child

end EbnfExpr

namespace GrammarSite

private theorem selected_eq_some (site : GrammarSite) :
    (m2cV1.rhs site.val.rule).nodeAt? site.val.path =
      some site.expression := by
  apply Option.eq_some_iff_get_eq.mpr
  exact ⟨site.property, rfl⟩

private theorem child_selected_eq_some
    (site : GrammarSite) (index : Nat) (child : EbnfExpr)
    (selected : site.expression.children[index]? = some child) :
    (m2cV1.rhs site.val.rule).nodeAt? (site.val.path ++ [index]) =
      some child := by
  rw [EbnfExpr.nodeAt?_append, selected_eq_some]
  simp [EbnfExpr.nodeAt?, selected]

private def childAt
    (site : GrammarSite) (index : Nat) (child : EbnfExpr)
    (selected : site.expression.children[index]? = some child) :
    GrammarSite :=
  ⟨{ rule := site.val.rule, path := site.val.path ++ [index] }, by
    simp [GrammarSiteKey.valid,
      child_selected_eq_some site index child selected]⟩

private theorem childAt_expression
    (site : GrammarSite) (index : Nat) (child : EbnfExpr)
    (selected : site.expression.children[index]? = some child) :
    (childAt site index child selected).expression = child := by
  unfold GrammarSite.expression childAt
  rcases Option.eq_some_iff_get_eq.mp
      (child_selected_eq_some site index child selected) with
    ⟨isSome, result⟩
  exact result

private def directChildren (site : GrammarSite) : List GrammarSite :=
  List.ofFn fun index : Fin site.expression.children.length =>
    childAt site index.val site.expression.children[index.val]
      (List.getElem?_eq_getElem index.isLt)

private theorem directChildren_expression (site : GrammarSite) :
    (directChildren site).map GrammarSite.expression =
      site.expression.children := by
  rw [directChildren, List.map_ofFn]
  have expressions :
      GrammarSite.expression ∘
          (fun index : Fin site.expression.children.length =>
            childAt site index.val site.expression.children[index.val]
              (List.getElem?_eq_getElem index.isLt)) =
        (fun index : Fin site.expression.children.length =>
          site.expression.children[index.val]) := by
    funext index
    exact childAt_expression site index.val site.expression.children[index.val]
      (List.getElem?_eq_getElem index.isLt)
  rw [expressions, List.ofFn_getElem]

end GrammarSite

private def grammarSiteKeysForRule
    (rule : GrammarRuleId) : List GrammarSiteKey :=
  ((m2cV1.rhs rule).sitePaths.map fun path => { rule, path })

/-- Every grammar site in rule order and lexicographic path order. -/
def allGrammarSites : List GrammarSite :=
  (allGrammarRuleIds.flatMap grammarSiteKeysForRule).filterMap
    GrammarSite.ofKey?

namespace GrammarSite

/-- The stable zero-based index in rule/path order. -/
def index (site : GrammarSite) : Nat :=
  allGrammarSites.findIdx fun candidate => candidate.val == site.val

/-- Compare sites by rule order and lexicographic child path. -/
protected def compare (left right : GrammarSite) : Ordering :=
  compare left.index right.index

instance : Ord GrammarSite := ⟨GrammarSite.compare⟩

end GrammarSite

/-- The finite EBNF node kinds used to refine grammar sites. -/
inductive EbnfNodeKind where
  | atom
  | sequence
  | group
  | choice
  | optional
  | star
  | plus
  | list0
  | list1
  deriving Repr, BEq, DecidableEq

namespace EbnfExpr

/-- The outer constructor kind of one EBNF node. -/
def kind : EbnfExpr → EbnfNodeKind
  | .atom _ => .atom
  | .sequence _ => .sequence
  | .group _ => .group
  | .choice _ => .choice
  | .optional _ => .optional
  | .star _ => .star
  | .plus _ => .plus
  | .list0 _ => .list0
  | .list1 _ => .list1

/-- The displayed choice arity, or zero for another node kind. -/
def choiceBranchCount : EbnfExpr → Nat
  | .choice branches => branches.length
  | _ => 0

end EbnfExpr

/-- A grammar site refined by its exact EBNF node kind. -/
structure GrammarSiteOfKind (kind : EbnfNodeKind) where
  site : GrammarSite
  hasKind : site.expression.kind = kind
  deriving Repr, DecidableEq

namespace GrammarSiteOfKind

/-- Check one grammar site against an expected node kind. -/
def ofSite? (kind : EbnfNodeKind)
    (site : GrammarSite) : Option (GrammarSiteOfKind kind) :=
  if hasKind : site.expression.kind = kind then
    some ⟨site, hasKind⟩
  else
    none

end GrammarSiteOfKind

abbrev AtomSite := GrammarSiteOfKind .atom
abbrev SequenceSite := GrammarSiteOfKind .sequence
abbrev GroupSite := GrammarSiteOfKind .group
abbrev ChoiceSite := GrammarSiteOfKind .choice
abbrev OptionalSite := GrammarSiteOfKind .optional
abbrev StarSite := GrammarSiteOfKind .star
abbrev PlusSite := GrammarSiteOfKind .plus
abbrev List0Site := GrammarSiteOfKind .list0
abbrev List1Site := GrammarSiteOfKind .list1

namespace SequenceSite

/-- The direct sequence children in displayed order. -/
def children (site : SequenceSite) : List GrammarSite :=
  GrammarSite.directChildren site.site

/-- Sequence child sites select exactly the displayed child expressions. -/
theorem children_expression (site : SequenceSite) :
    (site.children.map GrammarSite.expression) =
      site.site.expression.children :=
  GrammarSite.directChildren_expression site.site

/-- A sequence site has the expected outer shape and ordered children. -/
theorem expression_eq_sequence (site : SequenceSite) :
    site.site.expression =
      EbnfExpr.sequence (site.children.map GrammarSite.expression) := by
  rw [children_expression]
  have hasKind := site.hasKind
  cases expression : site.site.expression <;>
    simp [EbnfExpr.kind, EbnfExpr.children, expression] at hasKind ⊢

end SequenceSite

private inductive UnarySiteKind where
  | group
  | optional
  | star
  | plus
  | list0
  | list1

namespace UnarySiteKind

private def nodeKind : UnarySiteKind → EbnfNodeKind
  | .group => .group
  | .optional => .optional
  | .star => .star
  | .plus => .plus
  | .list0 => .list0
  | .list1 => .list1

private def apply : UnarySiteKind → EbnfExpr → EbnfExpr
  | .group => .group
  | .optional => .optional
  | .star => .star
  | .plus => .plus
  | .list0 => .list0
  | .list1 => .list1

end UnarySiteKind

private theorem unaryChild_isSome
    (kind : UnarySiteKind)
    (site : GrammarSiteOfKind kind.nodeKind) :
    site.site.expression.children[0]?.isSome = true := by
  have hasKind := site.hasKind
  cases kind <;>
    cases expression : site.site.expression <;>
      simp [UnarySiteKind.nodeKind, EbnfExpr.kind,
        EbnfExpr.children, expression] at hasKind ⊢

private def unaryChildExpression
    (kind : UnarySiteKind)
    (site : GrammarSiteOfKind kind.nodeKind) : EbnfExpr :=
  site.site.expression.children[0]?.get (unaryChild_isSome kind site)

private theorem unaryChildExpression_selected
    (kind : UnarySiteKind)
    (site : GrammarSiteOfKind kind.nodeKind) :
    site.site.expression.children[0]? =
      some (unaryChildExpression kind site) := by
  apply Option.eq_some_iff_get_eq.mpr
  exact ⟨unaryChild_isSome kind site, rfl⟩

private def unaryChild
    (kind : UnarySiteKind)
    (site : GrammarSiteOfKind kind.nodeKind) : GrammarSite :=
  GrammarSite.childAt site.site 0 (unaryChildExpression kind site)
    (unaryChildExpression_selected kind site)

private theorem unaryChild_expression
    (kind : UnarySiteKind)
    (site : GrammarSiteOfKind kind.nodeKind) :
    (unaryChild kind site).expression = unaryChildExpression kind site :=
  GrammarSite.childAt_expression site.site 0 (unaryChildExpression kind site)
    (unaryChildExpression_selected kind site)

private theorem unaryExpression_eq
    (kind : UnarySiteKind)
    (site : GrammarSiteOfKind kind.nodeKind) :
    site.site.expression = kind.apply (unaryChild kind site).expression := by
  have hasKind := site.hasKind
  have childExpression := unaryChild_expression kind site
  cases kind <;>
    cases expression : site.site.expression <;>
      simp [UnarySiteKind.nodeKind, EbnfExpr.kind, expression] at hasKind
  all_goals
    simp [unaryChildExpression, EbnfExpr.children, expression] at childExpression
    simp [UnarySiteKind.apply, childExpression]

namespace GroupSite

/-- The unique direct child of a grouping site. -/
def child (site : GroupSite) : GrammarSite :=
  unaryChild .group site

/-- A grouping site has the expected outer shape and child. -/
theorem expression_eq_group (site : GroupSite) :
    site.site.expression = EbnfExpr.group site.child.expression :=
  unaryExpression_eq .group site

end GroupSite

namespace OptionalSite

/-- The unique direct child of an optional site. -/
def child (site : OptionalSite) : GrammarSite :=
  unaryChild .optional site

/-- An optional site has the expected outer shape and child. -/
theorem expression_eq_optional (site : OptionalSite) :
    site.site.expression = EbnfExpr.optional site.child.expression :=
  unaryExpression_eq .optional site

end OptionalSite

namespace StarSite

/-- The unique repeated child of a star site. -/
def child (site : StarSite) : GrammarSite :=
  unaryChild .star site

/-- A star site has the expected outer shape and child. -/
theorem expression_eq_star (site : StarSite) :
    site.site.expression = EbnfExpr.star site.child.expression :=
  unaryExpression_eq .star site

end StarSite

namespace PlusSite

/-- The unique repeated child of a plus site. -/
def child (site : PlusSite) : GrammarSite :=
  unaryChild .plus site

/-- A plus site has the expected outer shape and child. -/
theorem expression_eq_plus (site : PlusSite) :
    site.site.expression = EbnfExpr.plus site.child.expression :=
  unaryExpression_eq .plus site

end PlusSite

namespace List0Site

/-- The repeated element site of a zero-or-more comma list. -/
def element (site : List0Site) : GrammarSite :=
  unaryChild .list0 site

/-- A zero-or-more list site has the expected outer shape and element. -/
theorem expression_eq_list0 (site : List0Site) :
    site.site.expression = EbnfExpr.list0 site.element.expression :=
  unaryExpression_eq .list0 site

end List0Site

namespace List1Site

/-- The repeated element site of a one-or-more comma list. -/
def element (site : List1Site) : GrammarSite :=
  unaryChild .list1 site

/-- A one-or-more list site has the expected outer shape and element. -/
theorem expression_eq_list1 (site : List1Site) :
    site.site.expression = EbnfExpr.list1 site.element.expression :=
  unaryExpression_eq .list1 site

end List1Site

private def sitesOfKind
    (kind : EbnfNodeKind) : List (GrammarSiteOfKind kind) :=
  allGrammarSites.filterMap (GrammarSiteOfKind.ofSite? kind)

def allAtomSites : List AtomSite := sitesOfKind .atom
def allSequenceSites : List SequenceSite := sitesOfKind .sequence
def allGroupSites : List GroupSite := sitesOfKind .group
def allChoiceSites : List ChoiceSite := sitesOfKind .choice
def allOptionalSites : List OptionalSite := sitesOfKind .optional
def allStarSites : List StarSite := sitesOfKind .star
def allPlusSites : List PlusSite := sitesOfKind .plus
def allList0Sites : List List0Site := sitesOfKind .list0
def allList1Sites : List List1Site := sitesOfKind .list1

namespace ChoiceSite

/-- The exact displayed branch count of a choice site. -/
def branchCount (site : ChoiceSite) : Nat :=
  site.site.expression.choiceBranchCount

/-- The displayed choice branches in exact source order. -/
def branchExpressions (site : ChoiceSite) :
    Vector EbnfExpr site.branchCount :=
  ⟨site.site.expression.children.toArray, by
    have hasKind := site.hasKind
    cases expression : site.site.expression <;>
      simp [ChoiceSite.branchCount, EbnfExpr.choiceBranchCount,
        EbnfExpr.kind, EbnfExpr.children, expression] at hasKind ⊢⟩

/-- A choice site has the expected outer shape and displayed branches. -/
theorem expression_eq_choice (site : ChoiceSite) :
    site.site.expression =
      EbnfExpr.choice site.branchExpressions.toList := by
  have hasKind := site.hasKind
  cases expression : site.site.expression <;>
    simp [EbnfExpr.kind, expression] at hasKind
  simp [branchExpressions, EbnfExpr.children, expression, Vector.toList]

private def branchChildIndex
    (site : ChoiceSite) (branch : Fin site.branchCount) :
    Fin site.site.expression.children.length :=
  ⟨branch.val, by
    have hasKind := site.hasKind
    cases expression : site.site.expression <;>
      simp [EbnfExpr.kind, expression] at hasKind
    simpa [ChoiceSite.branchCount, EbnfExpr.choiceBranchCount,
      EbnfExpr.children, expression] using branch.isLt⟩

private theorem branchExpression_eq
    (site : ChoiceSite) (branch : Fin site.branchCount) :
    site.site.expression.children[(branchChildIndex site branch).val] =
      site.branchExpressions.get branch := by
  simp [branchChildIndex, branchExpressions, Vector.get]

private theorem branch_selected_eq_some
    (site : ChoiceSite) (branch : Fin site.branchCount) :
    site.site.expression.children[branch.val]? =
      some (site.branchExpressions.get branch) := by
  have inBounds : branch.val < site.site.expression.children.length :=
    (branchChildIndex site branch).isLt
  rw [List.getElem?_eq_getElem inBounds]
  exact congrArg some (branchExpression_eq site branch)

/-- Select one displayed choice branch as a checked grammar site. -/
def branch (site : ChoiceSite)
    (branch : Fin site.branchCount) : GrammarSite :=
  GrammarSite.childAt site.site branch.val
    (site.branchExpressions.get branch)
    (branch_selected_eq_some site branch)

/-- A selected branch site has exactly the indexed branch expression. -/
theorem branch_expression
    (site : ChoiceSite) (branch : Fin site.branchCount) :
    (site.branch branch).expression =
      site.branchExpressions.get branch :=
  GrammarSite.childAt_expression site.site branch.val
    (site.branchExpressions.get branch)
    (branch_selected_eq_some site branch)

/-- All checked branch sites in displayed choice order. -/
def branches (site : ChoiceSite) :
    Vector GrammarSite site.branchCount :=
  Vector.ofFn site.branch

/-- Convert a branch index to the branch-expression list index. -/
def branchListIndex (site : ChoiceSite)
    (branch : Fin site.branchCount) :
    Fin site.branchExpressions.toList.length :=
  ⟨branch.val, by simp⟩

/-- Branch-list index conversion preserves the numeric index. -/
theorem branchListIndex_val
    (site : ChoiceSite) (branch : Fin site.branchCount) :
    (site.branchListIndex branch).val = branch.val :=
  rfl

/-- Branch list lookup agrees with vector lookup at the converted index. -/
theorem branch_get_toList
    (site : ChoiceSite) (branch : Fin site.branchCount) :
    site.branchExpressions.toList.get (site.branchListIndex branch) =
      site.branchExpressions.get branch := by
  change site.branchExpressions.toList[branch.val] =
    site.branchExpressions.get branch
  exact Vector.getElem_toList (site.branchListIndex branch).isLt

end ChoiceSite

/-- The disjoint union of comma-list sites that own tail auxiliaries. -/
inductive ListSite where
  | list0 (site : List0Site)
  | list1 (site : List1Site)
  deriving Repr, DecidableEq

namespace ListSite

/-- The repeated element site owned by a comma-list site. -/
def element : ListSite → GrammarSite
  | .list0 site => site.element
  | .list1 site => site.element

/-- The element projection reduces directly for a zero-or-more list site. -/
theorem element_list0 (site : List0Site) :
    (ListSite.list0 site).element = site.element :=
  rfl

/-- The element projection reduces directly for a one-or-more list site. -/
theorem element_list1 (site : List1Site) :
    (ListSite.list1 site).element = site.element :=
  rfl

end ListSite

private def listSiteOfGrammarSite? (site : GrammarSite) : Option ListSite :=
  match GrammarSiteOfKind.ofSite? .list0 site with
  | some list0Site => some (.list0 list0Site)
  | none =>
      match GrammarSiteOfKind.ofSite? .list1 site with
      | some list1Site => some (.list1 list1Site)
      | none => none

/-- All list sites in their owning grammar-site order. -/
def allListSites : List ListSite :=
  allGrammarSites.filterMap listSiteOfGrammarSite?

mutual

private def nullableExpr
    (nullableRules : List GrammarRuleId) : EbnfExpr → Bool
  | .atom (.terminal _) => false
  | .atom (.nonterminal rule) => nullableRules.contains rule
  | .sequence children => (nullableExprValues nullableRules children).all id
  | .group child => nullableExpr nullableRules child
  | .choice branches => (nullableExprValues nullableRules branches).any id
  | .optional _ => true
  | .star _ => true
  | .plus child => nullableExpr nullableRules child
  | .list0 _ => true
  | .list1 element => nullableExpr nullableRules element

private def nullableExprValues
    (nullableRules : List GrammarRuleId) : List EbnfExpr → List Bool
  | [] => []
  | head :: tail =>
      nullableExpr nullableRules head ::
        nullableExprValues nullableRules tail

end

private def nullableStep
    (nullableRules : List GrammarRuleId) : List GrammarRuleId :=
  allGrammarRuleIds.filter fun rule =>
    nullableRules.contains rule || nullableExpr nullableRules (m2cV1.rhs rule)

private def nullableClosure : Nat → List GrammarRuleId → List GrammarRuleId
  | 0, nullableRules => nullableRules
  | fuel + 1, nullableRules =>
      nullableClosure fuel (nullableStep nullableRules)

/-- The least nullable-rule set, reached within the finite rule count. -/
def nullableGrammarRules : List GrammarRuleId :=
  nullableClosure allGrammarRuleIds.length []

/-- True exactly when a repetition site has a nullable repeated element. -/
def repeatedElementNullable (site : GrammarSite) : Bool :=
  match site.expression with
  | .star element
  | .plus element
  | .list0 element
  | .list1 element => nullableExpr nullableGrammarRules element
  | _ => false

mutual

private def repetitionsNonnullableExpr
    (nullableRules : List GrammarRuleId) : EbnfExpr → Bool
  | .atom _ => true
  | .sequence children
  | .choice children =>
      repetitionsNonnullableExprValues nullableRules children
  | .group child
  | .optional child => repetitionsNonnullableExpr nullableRules child
  | .star child
  | .plus child
  | .list0 child
  | .list1 child =>
      !nullableExpr nullableRules child &&
        repetitionsNonnullableExpr nullableRules child

private def repetitionsNonnullableExprValues
    (nullableRules : List GrammarRuleId) : List EbnfExpr → Bool
  | [] => true
  | head :: tail =>
      repetitionsNonnullableExpr nullableRules head &&
        repetitionsNonnullableExprValues nullableRules tail

end

/-- The expansion precondition forbidding nullable repeated elements. -/
def repetitionsNonnullable : Bool :=
  allGrammarRuleIds.all fun rule =>
    repetitionsNonnullableExpr nullableGrammarRules (m2cV1.rhs rule)

/-- The two branches of an optional EBNF node. -/
inductive OptionalBranch where
  | none
  | some
  deriving Repr, BEq, DecidableEq

/-- The empty and extending branches of star and comma-tail nodes. -/
inductive NilConsBranch where
  | nil
  | cons
  deriving Repr, BEq, DecidableEq

/-- The singleton and extending branches of a plus node. -/
inductive OneConsBranch where
  | one
  | cons
  deriving Repr, BEq, DecidableEq

/-- Stable IDs generated solely from the EBNF node table. -/
inductive ProductionId where
  | root (rule : GrammarRuleId)
  | atom (site : AtomSite)
  | seq (site : SequenceSite)
  | group (site : GroupSite)
  | choice (site : ChoiceSite) (branch : Fin site.branchCount)
  | opt (site : OptionalSite) (branch : OptionalBranch)
  | star (site : StarSite) (branch : NilConsBranch)
  | plus (site : PlusSite) (branch : OneConsBranch)
  | list0 (site : List0Site) (branch : NilConsBranch)
  | list1 (site : List1Site)
  | tail (site : ListSite) (branch : NilConsBranch)
  deriving Repr, DecidableEq

instance : BEq ProductionId :=
  ⟨fun left right => decide (left = right)⟩

/-- The one-to-one action ID owned by an expanded production. -/
inductive ActionId where
  | actionFor (production : ProductionId)
  deriving Repr, DecidableEq

instance : BEq ActionId :=
  ⟨fun left right => decide (left = right)⟩

namespace ActionId

/-- Recover the unique production owning an action. -/
def production : ActionId → ProductionId
  | .actionFor production => production

@[simp] theorem production_actionFor (production : ProductionId) :
    (ActionId.actionFor production).production = production :=
  rfl

@[simp] theorem actionFor_production (action : ActionId) :
    ActionId.actionFor action.production = action := by
  cases action
  rfl

end ActionId

/-- A source, site auxiliary, or comma-tail BNF nonterminal. -/
inductive NonterminalSymbol where
  | rule (rule : GrammarRuleId)
  | aux (site : GrammarSite)
  | tail (site : ListSite)
  deriving Repr, DecidableEq

instance : BEq NonterminalSymbol :=
  ⟨fun left right => decide (left = right)⟩

/-- One terminal or nonterminal symbol in an expanded BNF right-hand side. -/
inductive GrammarSymbol where
  | terminal (terminal : TerminalSymbol)
  | nonterminal (nonterminal : NonterminalSymbol)
  deriving Repr, DecidableEq

instance : BEq GrammarSymbol :=
  ⟨fun left right => decide (left = right)⟩

namespace EbnfAtom

/-- Translate one source EBNF atom to its expanded grammar symbol. -/
def grammarSymbol (atom : EbnfAtom) : GrammarSymbol :=
  match atom with
  | .terminal value => GrammarSymbol.terminal value
  | .nonterminal rule => GrammarSymbol.nonterminal (.rule rule)

end EbnfAtom

namespace EbnfExpr

private def atom? : EbnfExpr → Option EbnfAtom
  | EbnfExpr.atom value => some value
  | _ => none

end EbnfExpr

namespace AtomSite

private theorem atom?_isSome (site : AtomSite) :
    site.site.expression.atom?.isSome = true := by
  have hasKind := site.hasKind
  cases expression : site.site.expression <;>
    simp [EbnfExpr.atom?, EbnfExpr.kind, expression] at hasKind ⊢

/-- The exact atom selected by an atom site. -/
def atom (site : AtomSite) : EbnfAtom :=
  site.site.expression.atom?.get site.atom?_isSome

/-- The expanded grammar symbol selected by an atom site. -/
def symbol (site : AtomSite) : GrammarSymbol :=
  site.atom.grammarSymbol

/-- An atom site has the expected outer shape and selected atom. -/
theorem expression_eq_atom (site : AtomSite) :
    site.site.expression = EbnfExpr.atom site.atom := by
  have kind := site.hasKind
  cases expression : site.site.expression <;>
    simp [EbnfExpr.kind, expression] at kind
  congr 1
  unfold AtomSite.atom
  change _ =
    (match site.site.expression with
      | .atom value => some value
      | _ => none).get _
  simp [expression]

/-- Atom-site symbol selection agrees with atom translation. -/
theorem symbol_eq (site : AtomSite) :
    site.symbol = site.atom.grammarSymbol :=
  rfl

end AtomSite

namespace ListSite

/-- The EBNF site that owns this comma-tail auxiliary. -/
def owner : ListSite → GrammarSite
  | .list0 site => site.site
  | .list1 site => site.site

end ListSite

namespace ProductionId

/-- The exact expanded left-hand side. -/
def lhs : ProductionId → NonterminalSymbol
  | .root rule => .rule rule
  | .atom site => .aux site.site
  | .seq site => .aux site.site
  | .group site => .aux site.site
  | .choice site _ => .aux site.site
  | .opt site _ => .aux site.site
  | .star site _ => .aux site.site
  | .plus site _ => .aux site.site
  | .list0 site _ => .aux site.site
  | .list1 site => .aux site.site
  | .tail site _ => .tail site

/-- The exact expanded right-hand side, with epsilon represented by `[]`. -/
def rhs : ProductionId → List GrammarSymbol
  | .root rule =>
      [.nonterminal (.aux (GrammarSite.root rule))]
  | .atom site =>
      [site.symbol]
  | .seq site =>
      site.children.map fun child => .nonterminal (.aux child)
  | .group site =>
      [.nonterminal (.aux site.child)]
  | .choice site branch =>
      [.nonterminal (.aux (site.branch branch))]
  | .opt _ .none =>
      []
  | .opt site .some =>
      [.nonterminal (.aux site.child)]
  | .star _ .nil =>
      []
  | .star site .cons =>
      [.nonterminal (.aux site.child), .nonterminal (.aux site.site)]
  | .plus site .one =>
      [.nonterminal (.aux site.child)]
  | .plus site .cons =>
      [.nonterminal (.aux site.child), .nonterminal (.aux site.site)]
  | .list0 _ .nil =>
      []
  | .list0 site .cons =>
      [.nonterminal (.aux site.element),
        .nonterminal (.tail (.list0 site))]
  | .list1 site =>
      [.nonterminal (.aux site.element),
        .nonterminal (.tail (.list1 site))]
  | .tail _ .nil =>
      []
  | .tail site .cons =>
      [.terminal (.symbol .comma),
        .nonterminal (.aux site.element),
        .nonterminal (.tail site)]

/-- The root-production RHS layout. -/
@[simp] theorem rhs_root (rule : GrammarRuleId) :
    rhs (.root rule) =
      [.nonterminal (.aux (GrammarSite.root rule))] :=
  rfl

/-- The atom-production RHS layout. -/
@[simp] theorem rhs_atom (site : AtomSite) :
    rhs (.atom site) = [site.symbol] :=
  rfl

/-- The sequence-production RHS layout. -/
@[simp] theorem rhs_seq (site : SequenceSite) :
    rhs (.seq site) =
      site.children.map fun child => .nonterminal (.aux child) :=
  rfl

/-- The grouping-production RHS layout. -/
@[simp] theorem rhs_group (site : GroupSite) :
    rhs (.group site) = [.nonterminal (.aux site.child)] :=
  rfl

/-- The choice-production RHS layout. -/
@[simp] theorem rhs_choice
    (site : ChoiceSite) (branch : Fin site.branchCount) :
    rhs (.choice site branch) =
      [.nonterminal (.aux (site.branch branch))] :=
  rfl

/-- The empty optional-production RHS layout. -/
@[simp] theorem rhs_opt_none (site : OptionalSite) :
    rhs (.opt site .none) = [] :=
  rfl

/-- The present optional-production RHS layout. -/
@[simp] theorem rhs_opt_some (site : OptionalSite) :
    rhs (.opt site .some) = [.nonterminal (.aux site.child)] :=
  rfl

/-- The empty star-production RHS layout. -/
@[simp] theorem rhs_star_nil (site : StarSite) :
    rhs (.star site .nil) = [] :=
  rfl

/-- The extending star-production RHS layout. -/
@[simp] theorem rhs_star_cons (site : StarSite) :
    rhs (.star site .cons) =
      [.nonterminal (.aux site.child), .nonterminal (.aux site.site)] :=
  rfl

/-- The singleton plus-production RHS layout. -/
@[simp] theorem rhs_plus_one (site : PlusSite) :
    rhs (.plus site .one) = [.nonterminal (.aux site.child)] :=
  rfl

/-- The extending plus-production RHS layout. -/
@[simp] theorem rhs_plus_cons (site : PlusSite) :
    rhs (.plus site .cons) =
      [.nonterminal (.aux site.child), .nonterminal (.aux site.site)] :=
  rfl

/-- The empty zero-or-more list-production RHS layout. -/
@[simp] theorem rhs_list0_nil (site : List0Site) :
    rhs (.list0 site .nil) = [] :=
  rfl

/-- The extending zero-or-more list-production RHS layout. -/
@[simp] theorem rhs_list0_cons (site : List0Site) :
    rhs (.list0 site .cons) =
      [.nonterminal (.aux site.element),
        .nonterminal (.tail (.list0 site))] :=
  rfl

/-- The one-or-more list-production RHS layout. -/
@[simp] theorem rhs_list1 (site : List1Site) :
    rhs (.list1 site) =
      [.nonterminal (.aux site.element),
        .nonterminal (.tail (.list1 site))] :=
  rfl

/-- The empty comma-tail-production RHS layout. -/
@[simp] theorem rhs_tail_nil (site : ListSite) :
    rhs (.tail site .nil) = [] :=
  rfl

/-- The extending comma-tail-production RHS layout. -/
@[simp] theorem rhs_tail_cons (site : ListSite) :
    rhs (.tail site .cons) =
      [.terminal (.symbol .comma),
        .nonterminal (.aux site.element),
        .nonterminal (.tail site)] :=
  rfl

end ProductionId

/-- Stable production IDs in the exact constructor and site order. -/
def allProductionIds : List ProductionId :=
  allGrammarRuleIds.map .root ++
  allAtomSites.map .atom ++
  allSequenceSites.map .seq ++
  allGroupSites.map .group ++
  (allChoiceSites.flatMap fun site =>
    (List.finRange site.branchCount).map fun branch =>
      .choice site branch) ++
  (allOptionalSites.flatMap fun site =>
    [.opt site .none, .opt site .some]) ++
  (allStarSites.flatMap fun site =>
    [.star site .nil, .star site .cons]) ++
  (allPlusSites.flatMap fun site =>
    [.plus site .one, .plus site .cons]) ++
  (allList0Sites.flatMap fun site =>
    [.list0 site .nil, .list0 site .cons]) ++
  allList1Sites.map .list1 ++
  (allListSites.flatMap fun site =>
    [.tail site .nil, .tail site .cons])

/-- Stable action IDs inherited from production order. -/
def allActionIds : List ActionId :=
  allProductionIds.map .actionFor

namespace ProductionId

/-- The stable zero-based production index. -/
def index (production : ProductionId) : Nat :=
  allProductionIds.findIdx (· == production)

/-- Compare productions by the normative expanded-table order. -/
protected def compare (left right : ProductionId) : Ordering :=
  compare left.index right.index

instance : Ord ProductionId := ⟨ProductionId.compare⟩

end ProductionId

namespace ActionId

/-- The stable zero-based action index. -/
def index (action : ActionId) : Nat :=
  action.production.index

/-- Compare actions by the index of their unique production. -/
protected def compare (left right : ActionId) : Ordering :=
  compare left.index right.index

instance : Ord ActionId := ⟨ActionId.compare⟩

end ActionId

/-- One mechanically expanded production and its unique action. -/
structure ExpandedProduction where
  id : ProductionId
  lhs : NonterminalSymbol
  rhs : List GrammarSymbol
  action : ActionId
  deriving Repr, DecidableEq

namespace ExpandedProduction

/-- Expand the unique table cell selected by a production ID. -/
def ofId (id : ProductionId) : ExpandedProduction := {
  id
  lhs := id.lhs
  rhs := id.rhs
  action := .actionFor id
}

end ExpandedProduction

/-- The complete finite expanded BNF production table. -/
structure ExpandedGrammar where
  productions : List ExpandedProduction
  deriving Repr, DecidableEq

namespace ExpandedGrammar

/-- The production count derived from the expanded table. -/
def productionCount (grammar : ExpandedGrammar) : Nat :=
  grammar.productions.length

end ExpandedGrammar

private def expandedUnchecked : ExpandedGrammar := {
  productions := allProductionIds.map ExpandedProduction.ofId
}

/-- Check the nullable-repetition precondition before producing the table. -/
def checkedExpansion : Option ExpandedGrammar :=
  if repetitionsNonnullable then some expandedUnchecked else none

theorem grammarRuleCount_eq_seventyFive :
    allGrammarRuleIds.length = 75 := by
  decide

private theorem nullableStep_empty :
    nullableStep [] = [.optionalComma] := by
  rfl

private theorem nullableStep_optionalComma :
    nullableStep [.optionalComma] = [.optionalComma] := by
  rfl

private theorem nullableClosure_of_fixed
    (fuel : Nat) (rules : List GrammarRuleId)
    (fixed : nullableStep rules = rules) :
    nullableClosure fuel rules = rules := by
  induction fuel with
  | zero => rfl
  | succ fuel inductionHypothesis =>
      simp only [nullableClosure, fixed, inductionHypothesis]

theorem nullableGrammarRules_eq :
    nullableGrammarRules = [.optionalComma] := by
  change nullableClosure 75 [] = [.optionalComma]
  rw [show 75 = 74 + 1 by rfl]
  simp only [nullableClosure, nullableStep_empty]
  exact nullableClosure_of_fixed 74 [.optionalComma]
    nullableStep_optionalComma

private theorem repetitionsNonnullableExpr_m2cV1
    (rule : GrammarRuleId) :
    repetitionsNonnullableExpr nullableGrammarRules (m2cV1.rhs rule) = true := by
  rw [nullableGrammarRules_eq]
  cases rule <;> rfl

theorem repetitionsNonnullable_eq_true :
    repetitionsNonnullable = true := by
  simp [repetitionsNonnullable, repetitionsNonnullableExpr_m2cV1]

/-- The checked m2c-v1 expansion. -/
def expanded : ExpandedGrammar :=
  checkedExpansion.get (by
    simp [checkedExpansion, repetitionsNonnullable_eq_true])

/-- The exact production count derived from `expanded`. -/
def productionCount : Nat :=
  expanded.productionCount

/-- A stable production together with one legal dotted RHS cursor. -/
structure DottedRhs where
  production : ProductionId
  dot : Fin (production.rhs.length + 1)
  deriving Repr, DecidableEq

namespace DottedRhs

/-- Compare dotted positions by production index, then dot index. -/
protected def compare (left right : DottedRhs) : Ordering :=
  match compare left.production.index right.production.index with
  | .lt => .lt
  | .gt => .gt
  | .eq => compare left.dot.val right.dot.val

instance : Ord DottedRhs := ⟨DottedRhs.compare⟩

end DottedRhs

/-- The dotted-production name used by chart consumers. -/
abbrev DottedProduction := DottedRhs

/-- The nine closed priority facts that resolve syntactic prefix overlap. -/
inductive PriorityGuardId where
  | G01_statementIf
  | G02_matchArmBoundary
  | G03_parameterComptime
  | G04_letComptime
  | G05_typeComptime
  | G06_patternComptime
  | G07_leadingDotArguments
  | G08_terminalExpression
  | G09_genericContext
  deriving Repr, BEq, DecidableEq

/-- Priority guards in the displayed ADR order. -/
def allPriorityGuardIds : List PriorityGuardId := [
  .G01_statementIf,
  .G02_matchArmBoundary,
  .G03_parameterComptime,
  .G04_letComptime,
  .G05_typeComptime,
  .G06_patternComptime,
  .G07_leadingDotArguments,
  .G08_terminalExpression,
  .G09_genericContext
]

namespace PriorityGuardId

/-- The stable zero-based guard-table index. -/
def index (guard : PriorityGuardId) : Nat :=
  allPriorityGuardIds.findIdx (· == guard)

/-- Compare guards by their displayed finite-table order. -/
protected def compare
    (left right : PriorityGuardId) : Ordering :=
  compare left.index right.index

instance : Ord PriorityGuardId := ⟨PriorityGuardId.compare⟩

end PriorityGuardId

/-- The sole diagnostic parse override, separate from priority guards. -/
inductive ParseOverrideId where
  | G10_repeatedNonAssociative
  deriving Repr, BEq, DecidableEq

/-- The complete parse-override table. -/
def allParseOverrideIds : List ParseOverrideId := [
  .G10_repeatedNonAssociative
]

/-- The closed outcome of one priority-guard decision. -/
inductive GuardDecision where
  | positive
  | negative
  | neutral
  deriving Repr, BEq, DecidableEq

/-- Select which side of a priority-guard decision a production requires. -/
inductive Polarity where
  | positive
  | negative
  deriving Repr, BEq, DecidableEq

namespace Polarity

/-- Test a closed guard decision against the production's required side. -/
def accepts : Polarity → GuardDecision → Bool
  | .positive, .positive => true
  | .positive, .negative => false
  | .positive, .neutral => true
  | .negative, .positive => false
  | .negative, .negative => true
  | .negative, .neutral => true

end Polarity

namespace GuardDecision

/-- `Polarity.accepts` with its arguments in decision-first order. -/
def allows (decision : GuardDecision) (polarity : Polarity) : Bool :=
  Polarity.accepts polarity decision

end GuardDecision

/-- The exhaustive priority-polarity allowance table. -/
theorem polarity_accepts_guardDecision_table
    (polarity : Polarity) (decision : GuardDecision) :
    Polarity.accepts polarity decision =
      match polarity, decision with
      | .positive, .positive => true
      | .positive, .negative => false
      | .positive, .neutral => true
      | .negative, .positive => false
      | .negative, .negative => true
      | .negative, .neutral => true := rfl

/-- The decision-first allowance test is definitionally the polarity test. -/
theorem guardDecision_allows_eq_accepts
    (decision : GuardDecision) (polarity : Polarity) :
    decision.allows polarity = Polarity.accepts polarity decision := rfl

namespace GrammarSite

/-- Test a site against an exact source rule and child-index path. -/
def isAt
    (site : GrammarSite) (rule : GrammarRuleId)
    (path : List Nat) : Bool :=
  site.val.rule == rule && site.val.path == path

end GrammarSite

/-- The exhaustive priority requirements on one expanded production. -/
def guardOf : ProductionId → List (PriorityGuardId × Polarity)
  | .choice site branch =>
      if site.site.isAt .statement [] && branch.val == 3 then
        [(.G01_statementIf, .positive)]
      else if site.site.isAt .statement [] && branch.val == 10 then
        [(.G01_statementIf, .negative)]
      else if site.site.isAt .type [] && branch.val == 0 then
        [(.G05_typeComptime, .positive)]
      else if site.site.isAt .type [] && branch.val == 1 then
        [(.G05_typeComptime, .negative)]
      else if site.site.isAt .pattern [] && branch.val == 3 then
        [(.G06_patternComptime, .positive)]
      else if site.site.isAt .pattern [] && branch.val == 4 then
        [(.G06_patternComptime, .negative)]
      else if site.site.isAt .postfixPart [] && branch.val == 0 then
        [(.G07_leadingDotArguments, .negative)]
      else if site.site.isAt .expressionStatement [] && branch.val == 1 then
        [(.G08_terminalExpression, .positive)]
      else
        []
  | .opt site branch =>
      if site.site.isAt .parameter [0] then
        [(.G03_parameterComptime,
          match branch with
          | .none => .negative
          | .some => .positive)]
      else if site.site.isAt .letBinding [2, 0, 1] then
        [(.G04_letComptime,
          match branch with
          | .none => .negative
          | .some => .positive)]
      else if site.site.isAt .atom [2, 2] then
        [(.G07_leadingDotArguments,
          match branch with
          | .none => .negative
          | .some => .positive)]
      else if site.site.isAt .genericPrefix [1] then
        [(.G09_genericContext,
          match branch with
          | .none => .negative
          | .some => .positive)]
      else
        []
  | .star site branch =>
      if site.site.isAt .matchArm [3] then
        [(.G02_matchArmBoundary,
          match branch with
          | .nil => .positive
          | .cons => .negative)]
      else
        []
  | _ => []

/-- A proof-free key for validating every guarded production table cell. -/
inductive GuardedProductionKey where
  | choice
      (rule : GrammarRuleId) (path : List Nat) (branch : Nat)
  | opt
      (rule : GrammarRuleId) (path : List Nat) (branch : OptionalBranch)
  | star
      (rule : GrammarRuleId) (path : List Nat) (branch : NilConsBranch)
  deriving Repr, BEq, DecidableEq

namespace ProductionId

/-- Erase site proofs from the production forms that may carry guards. -/
def guardedKey? : ProductionId → Option GuardedProductionKey
  | .choice site branch =>
      some (.choice site.site.val.rule site.site.val.path branch.val)
  | .opt site branch =>
      some (.opt site.site.val.rule site.site.val.path branch)
  | .star site branch =>
      some (.star site.site.val.rule site.site.val.path branch)
  | _ => none

end ProductionId

/-- One guard requirement paired with its proof-free production key. -/
structure GuardCell where
  production : GuardedProductionKey
  polarity : Polarity
  deriving Repr, BEq, DecidableEq

/-- The actual guarded cells for one guard, in production-table order. -/
def guardCells (guard : PriorityGuardId) : List GuardCell :=
  allProductionIds.flatMap fun production =>
    match production.guardedKey? with
    | none => []
    | some key =>
        (guardOf production).filterMap fun guarded =>
          if guarded.1 == guard then
            some { production := key, polarity := guarded.2 }
          else
            none

/-- The exact normative target cells for each priority guard. -/
def expectedGuardCells : PriorityGuardId → List GuardCell
  | .G01_statementIf => [
      ⟨.choice .statement [] 3, .positive⟩,
      ⟨.choice .statement [] 10, .negative⟩
    ]
  | .G02_matchArmBoundary => [
      ⟨.star .matchArm [3] .nil, .positive⟩,
      ⟨.star .matchArm [3] .cons, .negative⟩
    ]
  | .G03_parameterComptime => [
      ⟨.opt .parameter [0] .none, .negative⟩,
      ⟨.opt .parameter [0] .some, .positive⟩
    ]
  | .G04_letComptime => [
      ⟨.opt .letBinding [2, 0, 1] .none, .negative⟩,
      ⟨.opt .letBinding [2, 0, 1] .some, .positive⟩
    ]
  | .G05_typeComptime => [
      ⟨.choice .type [] 0, .positive⟩,
      ⟨.choice .type [] 1, .negative⟩
    ]
  | .G06_patternComptime => [
      ⟨.choice .pattern [] 3, .positive⟩,
      ⟨.choice .pattern [] 4, .negative⟩
    ]
  | .G07_leadingDotArguments => [
      ⟨.choice .postfixPart [] 0, .negative⟩,
      ⟨.opt .atom [2, 2] .none, .negative⟩,
      ⟨.opt .atom [2, 2] .some, .positive⟩
    ]
  | .G08_terminalExpression => [
      ⟨.choice .expressionStatement [] 1, .positive⟩
    ]
  | .G09_genericContext => [
      ⟨.opt .genericPrefix [1] .none, .negative⟩,
      ⟨.opt .genericPrefix [1] .some, .positive⟩
    ]

/-- Executable validation of exact guard target, polarity, and coverage. -/
def guardCoverageValid : Bool :=
  allPriorityGuardIds.all fun guard =>
    guardCells guard == expectedGuardCells guard

/-- The four finite memo-key families used by the optimized parser. -/
inductive FastMemoKeyKind where
  | rule (rule : GrammarRuleId)
  | site (site : GrammarSite)
  | guard (guard : PriorityGuardId)
  | action (action : ActionId)
  deriving Repr, DecidableEq

instance : BEq FastMemoKeyKind :=
  ⟨fun left right => decide (left = right)⟩

/-- Every fast memo-key kind in displayed constructor/table order. -/
def allFastMemoKeyKinds : List FastMemoKeyKind :=
  allGrammarRuleIds.map .rule ++
  allGrammarSites.map .site ++
  allPriorityGuardIds.map .guard ++
  allActionIds.map .action

namespace FastMemoKeyKind

/-- The stable zero-based memo-key-kind index. -/
def index (kind : FastMemoKeyKind) : Nat :=
  allFastMemoKeyKinds.findIdx (· == kind)

/-- Compare memo-key kinds by displayed constructor and table order. -/
protected def compare
    (left right : FastMemoKeyKind) : Ordering :=
  compare left.index right.index

instance : Ord FastMemoKeyKind := ⟨FastMemoKeyKind.compare⟩

end FastMemoKeyKind

/-- The total dotted-position count derived from expanded RHS lengths. -/
def D : Nat :=
  (expanded.productions.map fun production =>
    production.rhs.length + 1).sum

/-- The fast memo-key cardinality derived from its finite enumeration. -/
def F : Nat :=
  allFastMemoKeyKinds.length

theorem F_eq_displayed_cardinality :
    F = allGrammarRuleIds.length + allGrammarSites.length +
      allPriorityGuardIds.length + allActionIds.length := by
  simp [F, allFastMemoKeyKinds, Nat.add_assoc]

theorem actionFor_injective : Function.Injective ActionId.actionFor := by
  intro left right equality
  cases equality
  rfl

theorem allActionIds_exact :
    allActionIds = allProductionIds.map ActionId.actionFor :=
  rfl

theorem checkedExpansion_actions_exact
    (grammar : ExpandedGrammar)
    (accepted : checkedExpansion = some grammar) :
    grammar.productions.map ExpandedProduction.action = allActionIds := by
  unfold checkedExpansion at accepted
  split at accepted
  · simp only [Option.some.injEq] at accepted
    subst grammar
    simp [expandedUnchecked, allActionIds, ExpandedProduction.ofId]
  · simp at accepted

theorem expanded_actions_exact :
    expanded.productions.map ExpandedProduction.action = allActionIds := by
  simp [expanded, checkedExpansion, repetitionsNonnullable_eq_true,
    expandedUnchecked, allActionIds, ExpandedProduction.ofId]

end Solcore.Surface.Multi.Grammar
