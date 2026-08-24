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

/-- Test whether a source rule occurs as a nonterminal atom in an EBNF tree. -/
private def hasRuleRef (target : GrammarRuleId) : EbnfExpr → Bool
  | .atom (.terminal _) => false
  | .atom (.nonterminal rule) => rule == target
  | .sequence children
  | .choice children => hasRuleRefs target children
  | .group child
  | .optional child
  | .star child
  | .plus child
  | .list0 child
  | .list1 child => hasRuleRef target child

private def hasRuleRefs (target : GrammarRuleId) : List EbnfExpr → Bool
  | [] => false
  | child :: rest => hasRuleRef target child || hasRuleRefs target rest

end

private theorem hasRuleRefs_of_mem
    {target : GrammarRuleId} {child : EbnfExpr} {children : List EbnfExpr}
    (member : child ∈ children)
    (references : hasRuleRef target child = true) :
    hasRuleRefs target children = true := by
  induction children with
  | nil => simp at member
  | cons head rest induction =>
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · simp [hasRuleRefs, references]
      · simp [hasRuleRefs, induction member]

private theorem hasRuleRef_of_child_mem
    {target : GrammarRuleId} {root child : EbnfExpr}
    (member : child ∈ root.children)
    (references : hasRuleRef target child = true) :
    hasRuleRef target root = true := by
  cases root with
  | atom atom => simp [children] at member
  | sequence children => exact hasRuleRefs_of_mem member references
  | choice branches => exact hasRuleRefs_of_mem member references
  | group selected
  | optional selected
  | star selected
  | plus selected
  | list0 selected
  | list1 selected =>
      simp only [children, List.mem_singleton] at member
      subst child
      exact references

private theorem hasRuleRef_of_nodeAt?_eq_some
    {target : GrammarRuleId} {root selected : EbnfExpr} {path : List Nat}
    (lookup : root.nodeAt? path = some selected)
    (references : hasRuleRef target selected = true) :
    hasRuleRef target root = true := by
  induction path generalizing root with
  | nil =>
      simp only [nodeAt?, Option.some.injEq] at lookup
      subst selected
      exact references
  | cons index rest induction =>
      simp only [nodeAt?] at lookup
      cases selectedChild : root.children[index]? with
      | none => simp [selectedChild] at lookup
      | some child =>
          rw [selectedChild] at lookup
          exact hasRuleRef_of_child_mem
            (List.mem_of_getElem? selectedChild)
            (induction lookup)

mutual

private def choicesNonempty : EbnfExpr → Bool
  | .atom _ => true
  | .sequence children => choicesNonemptyValues children
  | .choice branches => !branches.isEmpty && choicesNonemptyValues branches
  | .group child
  | .optional child
  | .star child
  | .plus child
  | .list0 child
  | .list1 child => choicesNonempty child

private def choicesNonemptyValues : List EbnfExpr → Bool
  | [] => true
  | child :: rest =>
      choicesNonempty child && choicesNonemptyValues rest

end

private theorem choicesNonemptyValues_of_mem
    {child : EbnfExpr} {children : List EbnfExpr}
    (member : child ∈ children)
    (valid : choicesNonemptyValues children = true) :
    choicesNonempty child = true := by
  induction children with
  | nil => simp at member
  | cons head rest induction =>
      simp only [List.mem_cons] at member
      simp only [choicesNonemptyValues, Bool.and_eq_true] at valid
      rcases member with rfl | member
      · exact valid.1
      · exact induction member valid.2

private theorem choicesNonempty_of_child_mem
    {root child : EbnfExpr}
    (member : child ∈ root.children)
    (valid : choicesNonempty root = true) :
    choicesNonempty child = true := by
  cases root with
  | atom atom => simp [children] at member
  | sequence children =>
      exact choicesNonemptyValues_of_mem member valid
  | choice branches =>
      simp only [choicesNonempty, Bool.and_eq_true] at valid
      exact choicesNonemptyValues_of_mem member valid.2
  | group selected
  | optional selected
  | star selected
  | plus selected
  | list0 selected
  | list1 selected =>
      simp only [children, List.mem_singleton] at member
      subst child
      exact valid

private theorem choicesNonempty_of_nodeAt?_eq_some
    {root selected : EbnfExpr} {path : List Nat}
    (lookup : root.nodeAt? path = some selected)
    (valid : choicesNonempty root = true) :
    choicesNonempty selected = true := by
  induction path generalizing root with
  | nil =>
      simp only [nodeAt?, Option.some.injEq] at lookup
      subst selected
      exact valid
  | cons index rest induction =>
      simp only [nodeAt?] at lookup
      cases selectedChild : root.children[index]? with
      | none => simp [selectedChild] at lookup
      | some child =>
          rw [selectedChild] at lookup
          exact induction lookup
            (choicesNonempty_of_child_mem
              (List.mem_of_getElem? selectedChild) valid)

private theorem m2cV1_choicesNonempty (rule : GrammarRuleId) :
    choicesNonempty (m2cV1.rhs rule) = true := by
  cases rule <;> decide

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

/-- Every expanded sequence child remains inside its source rule. -/
theorem child_rule
    (site : SequenceSite) (child : GrammarSite)
    (member : child ∈ site.children) :
    child.val.rule = site.site.val.rule := by
  obtain ⟨index, rfl⟩ := List.get_of_mem member
  simp [children, GrammarSite.directChildren,
    GrammarSite.childAt]

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

/-- A grouping child remains inside its source rule. -/
@[simp] theorem child_rule (site : GroupSite) :
    site.child.val.rule = site.site.val.rule :=
  rfl

/-- A grouping site has the expected outer shape and child. -/
theorem expression_eq_group (site : GroupSite) :
    site.site.expression = EbnfExpr.group site.child.expression :=
  unaryExpression_eq .group site

end GroupSite

namespace OptionalSite

/-- The unique direct child of an optional site. -/
def child (site : OptionalSite) : GrammarSite :=
  unaryChild .optional site

/-- An optional child remains inside its source rule. -/
@[simp] theorem child_rule (site : OptionalSite) :
    site.child.val.rule = site.site.val.rule :=
  rfl

/-- An optional site has the expected outer shape and child. -/
theorem expression_eq_optional (site : OptionalSite) :
    site.site.expression = EbnfExpr.optional site.child.expression :=
  unaryExpression_eq .optional site

end OptionalSite

namespace StarSite

/-- The unique repeated child of a star site. -/
def child (site : StarSite) : GrammarSite :=
  unaryChild .star site

/-- A star child remains inside its source rule. -/
@[simp] theorem child_rule (site : StarSite) :
    site.child.val.rule = site.site.val.rule :=
  rfl

/-- A star site has the expected outer shape and child. -/
theorem expression_eq_star (site : StarSite) :
    site.site.expression = EbnfExpr.star site.child.expression :=
  unaryExpression_eq .star site

end StarSite

namespace PlusSite

/-- The unique repeated child of a plus site. -/
def child (site : PlusSite) : GrammarSite :=
  unaryChild .plus site

/-- A plus child remains inside its source rule. -/
@[simp] theorem child_rule (site : PlusSite) :
    site.child.val.rule = site.site.val.rule :=
  rfl

/-- A plus site has the expected outer shape and child. -/
theorem expression_eq_plus (site : PlusSite) :
    site.site.expression = EbnfExpr.plus site.child.expression :=
  unaryExpression_eq .plus site

end PlusSite

namespace List0Site

/-- The repeated element site of a zero-or-more comma list. -/
def element (site : List0Site) : GrammarSite :=
  unaryChild .list0 site

/-- A list-zero element remains inside its source rule. -/
@[simp] theorem element_rule (site : List0Site) :
    site.element.val.rule = site.site.val.rule :=
  rfl

/-- A zero-or-more list site has the expected outer shape and element. -/
theorem expression_eq_list0 (site : List0Site) :
    site.site.expression = EbnfExpr.list0 site.element.expression :=
  unaryExpression_eq .list0 site

end List0Site

namespace List1Site

/-- The repeated element site of a one-or-more comma list. -/
def element (site : List1Site) : GrammarSite :=
  unaryChild .list1 site

/-- A list-one element remains inside its source rule. -/
@[simp] theorem element_rule (site : List1Site) :
    site.element.val.rule = site.site.val.rule :=
  rfl

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

/-- Every checked choice site in the fixed source grammar has at least one
displayed branch. -/
theorem branchCount_pos (site : ChoiceSite) : 0 < site.branchCount := by
  have valid :
      ((m2cV1.rhs site.site.val.rule).nodeAt?
        site.site.val.path).isSome = true := by
    simpa [GrammarSiteKey.valid] using site.site.property
  have selected :
      (m2cV1.rhs site.site.val.rule).nodeAt? site.site.val.path =
        some site.site.expression := by
    apply Option.eq_some_iff_get_eq.mpr
    exact ⟨valid, rfl⟩
  have choices := EbnfExpr.choicesNonempty_of_nodeAt?_eq_some selected
    (EbnfExpr.m2cV1_choicesNonempty site.site.val.rule)
  have expression := expression_eq_choice site
  have nonempty : site.branchExpressions.toList ≠ [] := by
    intro empty
    rw [expression, empty] at choices
    simp [EbnfExpr.choicesNonempty] at choices
  unfold ChoiceSite.branchCount
  rw [expression]
  exact List.length_pos_iff.mpr nonempty

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

/-- A selected choice branch remains inside its source rule. -/
@[simp] theorem branch_rule
    (site : ChoiceSite) (selected : Fin site.branchCount) :
    (site.branch selected).val.rule = site.site.val.rule :=
  rfl

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

/-- The exact key of the match-arm pattern-list site. -/
private def matchArmPatternListSiteKey : GrammarSiteKey := {
  rule := .matchArm
  path := [1]
}

/-- The exact match-arm key resolves to a checked grammar site. -/
private theorem matchArmPatternGrammarSite_isSome :
    (GrammarSite.ofKey? matchArmPatternListSiteKey).isSome = true := by
  unfold matchArmPatternListSiteKey GrammarSite.ofKey?
    GrammarSiteKey.valid m2cV1
  simp [m2cV1Rhs, EbnfExpr.nodeAt?, EbnfExpr.children,
    sequence, symbol, list1, nonterminal]

/-- The checked grammar site selected by the exact match-arm key. -/
private def matchArmPatternGrammarSite : GrammarSite :=
  (GrammarSite.ofKey? matchArmPatternListSiteKey).get
    matchArmPatternGrammarSite_isSome

/-- The first checked lookup returns the exact selected grammar site. -/
private theorem matchArmPatternGrammarSite_some :
    GrammarSite.ofKey? matchArmPatternListSiteKey =
      some matchArmPatternGrammarSite := by
  apply Option.eq_some_iff_get_eq.mpr
  exact ⟨matchArmPatternGrammarSite_isSome, rfl⟩

/-- The selected match-arm grammar site has the checked list-one kind. -/
private theorem matchArmPatternListSite_isSome :
    (GrammarSiteOfKind.ofSite? .list1
      matchArmPatternGrammarSite).isSome = true := by
  unfold matchArmPatternGrammarSite matchArmPatternListSiteKey
    GrammarSiteOfKind.ofSite? GrammarSite.ofKey?
    GrammarSiteKey.valid GrammarSite.expression m2cV1
  simp [m2cV1Rhs, EbnfExpr.nodeAt?, EbnfExpr.children,
    EbnfExpr.kind, sequence, symbol, list1, nonterminal]

/-- The fixed comma-list site containing a match arm's displayed patterns. -/
def matchArmPatternListSite : List1Site :=
  (GrammarSiteOfKind.ofSite? .list1
    matchArmPatternGrammarSite).get matchArmPatternListSite_isSome

/-- The second checked lookup returns the exact refined list-one site. -/
private theorem matchArmPatternListSite_some :
    GrammarSiteOfKind.ofSite? .list1 matchArmPatternGrammarSite =
      some matchArmPatternListSite := by
  apply Option.eq_some_iff_get_eq.mpr
  exact ⟨matchArmPatternListSite_isSome, rfl⟩

/-- The fixed match-arm pattern-list site has its displayed grammar key. -/
theorem matchArmPatternListSite_key :
    matchArmPatternListSite.site.val =
      { rule := GrammarRuleId.matchArm, path := [1] } := by
  unfold matchArmPatternListSite matchArmPatternGrammarSite
    matchArmPatternListSiteKey GrammarSiteOfKind.ofSite?
    GrammarSite.ofKey? GrammarSiteKey.valid GrammarSite.expression m2cV1
  simp [m2cV1Rhs, EbnfExpr.nodeAt?, EbnfExpr.children,
    EbnfExpr.kind, sequence, symbol, list1, nonterminal]

/-- The fixed match-arm site is exactly the nonempty pattern list. -/
theorem matchArmPatternListSite_expression :
    matchArmPatternListSite.site.expression =
      EbnfExpr.list1
        (EbnfExpr.atom (EbnfAtom.nonterminal GrammarRuleId.pattern)) := by
  unfold matchArmPatternListSite matchArmPatternGrammarSite
    matchArmPatternListSiteKey GrammarSiteOfKind.ofSite?
    GrammarSite.ofKey? GrammarSiteKey.valid GrammarSite.expression m2cV1
  simp [m2cV1Rhs, EbnfExpr.nodeAt?, EbnfExpr.children,
    EbnfExpr.kind, sequence, symbol, list1, nonterminal]

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

private theorem rule_eq_postfix_of_references_atom
    (rule : GrammarRuleId) :
    EbnfExpr.hasRuleRef .atom (m2cV1.rhs rule) = true →
      rule = .postfix := by
  cases rule <;> decide

/-- The only atom site referring to the source `atom` rule belongs to the
source `postfix` rule. -/
theorem rule_eq_postfix_of_symbol_atom
    (site : AtomSite)
    (symbol : site.symbol =
      GrammarSymbol.nonterminal (.rule .atom)) :
    site.site.val.rule = .postfix := by
  have atom : site.atom = EbnfAtom.nonterminal .atom := by
    cases selected : site.atom with
    | terminal value =>
        simp [AtomSite.symbol, EbnfAtom.grammarSymbol, selected] at symbol
    | nonterminal rule =>
        have ruleEq : rule = .atom := by
          simpa [AtomSite.symbol, EbnfAtom.grammarSymbol, selected]
            using symbol
        simp [ruleEq]
  have expression : site.site.expression =
      EbnfExpr.atom (.nonterminal .atom) := by
    rw [AtomSite.expression_eq_atom, atom]
  have valid :
      ((m2cV1.rhs site.site.val.rule).nodeAt?
        site.site.val.path).isSome = true := by
    simpa [GrammarSiteKey.valid] using site.site.property
  have selected :
      (m2cV1.rhs site.site.val.rule).nodeAt? site.site.val.path =
        some site.site.expression := by
    apply Option.eq_some_iff_get_eq.mpr
    exact ⟨valid, rfl⟩
  exact rule_eq_postfix_of_references_atom _
    (EbnfExpr.hasRuleRef_of_nodeAt?_eq_some
      (selected.trans (congrArg some expression))
      rfl)

end AtomSite

namespace ListSite

/-- The EBNF site that owns this comma-tail auxiliary. -/
def owner : ListSite → GrammarSite
  | .list0 site => site.site
  | .list1 site => site.site

/-- A comma-list element remains inside the rule owning its tail. -/
@[simp] theorem element_rule (site : ListSite) :
    site.element.val.rule = site.owner.val.rule := by
  cases site <;> rfl

end ListSite

namespace ProductionId

/-- The source EBNF rule owning an expanded production. -/
def sourceRule : ProductionId → GrammarRuleId
  | .root rule => rule
  | .atom site => site.site.val.rule
  | .seq site => site.site.val.rule
  | .group site => site.site.val.rule
  | .choice site _ => site.site.val.rule
  | .opt site _ => site.site.val.rule
  | .star site _ => site.site.val.rule
  | .plus site _ => site.site.val.rule
  | .list0 site _ => site.site.val.rule
  | .list1 site => site.site.val.rule
  | .tail site _ => site.owner.val.rule

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

/-- Following an auxiliary nonterminal in an expanded right-hand side stays
inside the same source EBNF rule. -/
theorem sourceRule_eq_of_aux_mem_rhs
    (parent : ProductionId) (site : GrammarSite)
    (member : GrammarSymbol.nonterminal (.aux site) ∈ parent.rhs) :
    parent.sourceRule = site.val.rule := by
  cases parent with
  | root rule =>
      simp [rhs, sourceRule] at member ⊢
      subst site
      rfl
  | atom atomSite =>
      cases atomEq : atomSite.atom <;>
        simp [rhs, AtomSite.symbol,
          EbnfAtom.grammarSymbol, atomEq] at member
  | seq sequenceSite =>
      simp only [rhs, List.mem_map] at member
      rcases member with ⟨child, childMember, symbolEq⟩
      have siteEq : child = site := by
        exact NonterminalSymbol.aux.inj
          (GrammarSymbol.nonterminal.inj symbolEq)
      subst site
      exact (SequenceSite.child_rule sequenceSite child childMember).symm
  | group groupSite =>
      simp [rhs] at member
      subst site
      exact (GroupSite.child_rule groupSite).symm
  | choice choiceSite branch =>
      simp [rhs] at member
      subst site
      exact (ChoiceSite.branch_rule choiceSite branch).symm
  | opt optionalSite branch =>
      cases branch
      · simp [rhs] at member
      · simp [rhs] at member
        subst site
        exact (OptionalSite.child_rule optionalSite).symm
  | star starSite branch =>
      cases branch
      · simp [rhs] at member
      · simp only [rhs, List.mem_cons] at member
        rcases member with childEq | selfEq
        · simp at childEq
          subst site
          exact (StarSite.child_rule starSite).symm
        · simp at selfEq
          subst site
          rfl
  | plus plusSite branch =>
      cases branch
      · simp [rhs] at member
        subst site
        exact (PlusSite.child_rule plusSite).symm
      · simp only [rhs, List.mem_cons] at member
        rcases member with childEq | selfEq
        · simp at childEq
          subst site
          exact (PlusSite.child_rule plusSite).symm
        · simp at selfEq
          subst site
          rfl
  | list0 listSite branch =>
      cases branch
      · simp [rhs] at member
      · simp only [rhs, List.mem_cons] at member
        rcases member with elementEq | tailEq
        · simp at elementEq
          subst site
          exact (List0Site.element_rule listSite).symm
        · simp at tailEq
  | list1 listSite =>
      simp only [rhs, List.mem_cons] at member
      rcases member with elementEq | tailEq
      · simp at elementEq
        subst site
        exact (List1Site.element_rule listSite).symm
      · simp at tailEq
  | tail listSite branch =>
      cases branch
      · simp [rhs] at member
      · simp only [rhs, List.mem_cons] at member
        rcases member with terminalEq | elementEq | tailEq
        · simp at terminalEq
        · simp at elementEq
          subst site
          exact (ListSite.element_rule listSite).symm
        · simp at tailEq

/-- Following a comma-tail nonterminal in an expanded right-hand side stays
inside the same source EBNF rule. -/
theorem sourceRule_eq_of_tail_mem_rhs
    (parent : ProductionId) (site : ListSite)
    (member : GrammarSymbol.nonterminal (.tail site) ∈ parent.rhs) :
    parent.sourceRule = site.owner.val.rule := by
  cases parent with
  | root rule => simp [rhs] at member
  | atom atomSite =>
      cases atomEq : atomSite.atom <;>
        simp [rhs, AtomSite.symbol,
          EbnfAtom.grammarSymbol, atomEq] at member
  | seq sequenceSite => simp [rhs] at member
  | group groupSite => simp [rhs] at member
  | choice choiceSite branch => simp [rhs] at member
  | opt optionalSite branch => cases branch <;> simp [rhs] at member
  | star starSite branch => cases branch <;> simp [rhs] at member
  | plus plusSite branch => cases branch <;> simp [rhs] at member
  | list0 listSite branch =>
      cases branch
      · simp [rhs] at member
      · simp [rhs] at member
        subst site
        rfl
  | list1 listSite =>
      simp [rhs] at member
      subst site
      rfl
  | tail listSite branch =>
      cases branch
      · simp [rhs] at member
      · simp [rhs] at member
        subst site
        rfl

/-- An expanded right-hand side can refer to the source `atom` rule only from
a production owned by the source `postfix` rule. -/
theorem sourceRule_eq_postfix_of_rule_atom_mem_rhs
    (parent : ProductionId)
    (member : GrammarSymbol.nonterminal (.rule .atom) ∈ parent.rhs) :
    parent.sourceRule = .postfix := by
  cases parent with
  | root rule => simp [rhs] at member
  | atom site =>
      simp [rhs] at member
      exact AtomSite.rule_eq_postfix_of_symbol_atom site member.symm
  | seq site => simp [rhs] at member
  | group site => simp [rhs] at member
  | choice site branch => simp [rhs] at member
  | opt site branch => cases branch <;> simp [rhs] at member
  | star site branch => cases branch <;> simp [rhs] at member
  | plus site branch => cases branch <;> simp [rhs] at member
  | list0 site branch => cases branch <;> simp [rhs] at member
  | list1 site => simp [rhs] at member
  | tail site branch => cases branch <;> simp [rhs] at member

/-- A prediction entering the `postfix`/`atom` expansion region either starts
the postfix root or comes from a production already inside that region. -/
theorem enters_postfix_region_of_lhs_mem_rhs
    (parent predicted : ProductionId)
    (member : GrammarSymbol.nonterminal predicted.lhs ∈ parent.rhs)
    (inRegion : predicted.sourceRule = .postfix ∨
      predicted.sourceRule = .atom) :
    predicted = .root .postfix ∨
      parent.sourceRule = .postfix ∨
      parent.sourceRule = .atom := by
  cases predicted with
  | root rule =>
      rcases inRegion with inPostfix | inAtom
      · left
        simpa [sourceRule] using congrArg ProductionId.root inPostfix
      · right
        left
        have atomRule : rule = .atom := by
          simpa [sourceRule] using inAtom
        subst rule
        exact sourceRule_eq_postfix_of_rule_atom_mem_rhs parent
          (by simpa [lhs] using member)
  | atom site =>
      right
      rw [sourceRule_eq_of_aux_mem_rhs parent site.site
        (by simpa [lhs] using member)]
      simpa [sourceRule] using inRegion
  | seq site =>
      right
      rw [sourceRule_eq_of_aux_mem_rhs parent site.site
        (by simpa [lhs] using member)]
      simpa [sourceRule] using inRegion
  | group site =>
      right
      rw [sourceRule_eq_of_aux_mem_rhs parent site.site
        (by simpa [lhs] using member)]
      simpa [sourceRule] using inRegion
  | choice site branch =>
      right
      rw [sourceRule_eq_of_aux_mem_rhs parent site.site
        (by simpa [lhs] using member)]
      simpa [sourceRule] using inRegion
  | opt site branch =>
      right
      rw [sourceRule_eq_of_aux_mem_rhs parent site.site
        (by simpa [lhs] using member)]
      simpa [sourceRule] using inRegion
  | star site branch =>
      right
      rw [sourceRule_eq_of_aux_mem_rhs parent site.site
        (by simpa [lhs] using member)]
      simpa [sourceRule] using inRegion
  | plus site branch =>
      right
      rw [sourceRule_eq_of_aux_mem_rhs parent site.site
        (by simpa [lhs] using member)]
      simpa [sourceRule] using inRegion
  | list0 site branch =>
      right
      rw [sourceRule_eq_of_aux_mem_rhs parent site.site
        (by simpa [lhs] using member)]
      simpa [sourceRule] using inRegion
  | list1 site =>
      right
      rw [sourceRule_eq_of_aux_mem_rhs parent site.site
        (by simpa [lhs] using member)]
      simpa [sourceRule] using inRegion
  | tail site branch =>
      right
      rw [sourceRule_eq_of_tail_mem_rhs parent site
        (by simpa [lhs] using member)]
      simpa [sourceRule] using inRegion

end ProductionId

/-- Every outer production shape reduces to its complete public RHS bridge,
including every finite option and repetition branch. -/
theorem production_rhs_public_bridges_exact
    (production : ProductionId) :
    match production with
    | .root rule =>
        ProductionId.rhs (.root rule) =
          [.nonterminal (.aux (GrammarSite.root rule))]
    | .atom site =>
        ProductionId.rhs (.atom site) = [site.symbol]
    | .seq site =>
        ProductionId.rhs (.seq site) =
          site.children.map fun child => .nonterminal (.aux child)
    | .group site =>
        ProductionId.rhs (.group site) =
          [.nonterminal (.aux site.child)]
    | .choice site branch =>
        ProductionId.rhs (.choice site branch) =
          [.nonterminal (.aux (site.branch branch))]
    | .opt site branch =>
        match branch with
        | .none => ProductionId.rhs (.opt site .none) = []
        | .some => ProductionId.rhs (.opt site .some) =
            [.nonterminal (.aux site.child)]
    | .star site branch =>
        match branch with
        | .nil => ProductionId.rhs (.star site .nil) = []
        | .cons => ProductionId.rhs (.star site .cons) =
            [.nonterminal (.aux site.child),
              .nonterminal (.aux site.site)]
    | .plus site branch =>
        match branch with
        | .one => ProductionId.rhs (.plus site .one) =
            [.nonterminal (.aux site.child)]
        | .cons => ProductionId.rhs (.plus site .cons) =
            [.nonterminal (.aux site.child),
              .nonterminal (.aux site.site)]
    | .list0 site branch =>
        match branch with
        | .nil => ProductionId.rhs (.list0 site .nil) = []
        | .cons => ProductionId.rhs (.list0 site .cons) =
            [.nonterminal (.aux site.element),
              .nonterminal (.tail (.list0 site))]
    | .list1 site =>
        ProductionId.rhs (.list1 site) =
          [.nonterminal (.aux site.element),
            .nonterminal (.tail (.list1 site))]
    | .tail site branch =>
        match branch with
        | .nil => ProductionId.rhs (.tail site .nil) = []
        | .cons => ProductionId.rhs (.tail site .cons) =
            [.terminal (.symbol .comma),
              .nonterminal (.aux site.element),
              .nonterminal (.tail site)] := by
  cases production with
  | root rule => rfl
  | atom site => rfl
  | seq site => rfl
  | group site => rfl
  | choice site branch => rfl
  | opt site branch => cases branch <;> rfl
  | star site branch => cases branch <;> rfl
  | plus site branch => cases branch <;> rfl
  | list0 site branch => cases branch <;> rfl
  | list1 site => rfl
  | tail site branch => cases branch <;> rfl

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

namespace EbnfExpr

mutual

private theorem nodeAt?_isSome_implies_mem_paths
    (expression : EbnfExpr) (path : List Nat)
    (valid : (expression.nodeAt? path).isSome = true) :
    path ∈ paths expression := by
  cases expression with
  | atom atom =>
      cases path with
      | nil => simp [paths]
      | cons index rest =>
          simp [nodeAt?, children] at valid
  | sequence children
  | choice children =>
      cases path with
      | nil => simp [paths]
      | cons index rest =>
          unfold EbnfExpr.nodeAt? at valid
          unfold EbnfExpr.children at valid
          change (match children[index]? with
            | some child => child.nodeAt? rest
            | none => none).isSome = true at valid
          cases selected : children[index]? with
          | none => simp [selected] at valid
          | some child =>
              apply List.mem_cons_of_mem []
              simpa only [Nat.zero_add] using
                indexedChildPaths_complete children 0 index child rest
                  selected (by simpa only [selected, Option.isSome_some]
                    using valid)
  | group child
  | optional child
  | star child
  | plus child
  | list0 child
  | list1 child =>
      cases path with
      | nil => simp [paths]
      | cons index rest =>
          cases index with
          | zero =>
              apply List.mem_cons_of_mem []
              simp only [List.mem_map]
              exact ⟨rest,
                nodeAt?_isSome_implies_mem_paths child rest
                  (by simpa [nodeAt?, children] using valid), rfl⟩
          | succ index =>
              simp [nodeAt?, children] at valid

private theorem indexedChildPaths_complete
    (children : List EbnfExpr) (offset index : Nat)
    (child : EbnfExpr) (path : List Nat)
    (selected : children[index]? = some child)
    (valid : (child.nodeAt? path).isSome = true) :
    (offset + index) :: path ∈ indexedChildPaths offset children := by
  induction children generalizing offset index child with
  | nil => simp at selected
  | cons head tail induction =>
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at selected
          subst child
          simp only [Nat.add_zero, indexedChildPaths, List.mem_append,
            List.mem_map]
          exact Or.inl ⟨path,
            nodeAt?_isSome_implies_mem_paths head path valid, rfl⟩
      | succ index =>
          simp only [List.getElem?_cons_succ] at selected
          simp only [indexedChildPaths, List.mem_append]
          apply Or.inr
          simpa [Nat.add_assoc, Nat.add_comm 1 index] using
            induction (offset := offset + 1) (index := index)
              (child := child) selected valid

end

private theorem nodeAt?_isSome_implies_mem_sitePaths
    (expression : EbnfExpr) (path : List Nat)
    (valid : (expression.nodeAt? path).isSome = true) :
    path ∈ expression.sitePaths := by
  exact nodeAt?_isSome_implies_mem_paths expression path valid

end EbnfExpr

private theorem allGrammarRuleIds_complete (rule : GrammarRuleId) :
    rule ∈ allGrammarRuleIds := by
  cases rule <;> simp [allGrammarRuleIds]

private theorem grammarSiteKeysForRule_complete (site : GrammarSite) :
    site.val ∈ grammarSiteKeysForRule site.val.rule := by
  apply List.mem_map.mpr
  refine ⟨site.val.path, ?_, ?_⟩
  · exact EbnfExpr.nodeAt?_isSome_implies_mem_sitePaths
      (m2cV1.rhs site.val.rule) site.val.path site.property
  · cases site with
    | mk key valid => cases key; rfl

private theorem allGrammarSites_complete (site : GrammarSite) :
    site ∈ allGrammarSites := by
  apply List.mem_filterMap.mpr
  refine ⟨site.val, ?_, ?_⟩
  · apply List.mem_flatMap.mpr
    exact ⟨site.val.rule, allGrammarRuleIds_complete site.val.rule,
      grammarSiteKeysForRule_complete site⟩
  · unfold GrammarSite.ofKey?
    simp only [site.property, ↓reduceDIte]

private theorem sitesOfKind_complete
    {kind : EbnfNodeKind} (site : GrammarSiteOfKind kind) :
    site ∈ sitesOfKind kind := by
  apply List.mem_filterMap.mpr
  refine ⟨site.site, allGrammarSites_complete site.site, ?_⟩
  unfold GrammarSiteOfKind.ofSite?
  simp only [site.hasKind, ↓reduceDIte]

private theorem allListSites_complete (site : ListSite) :
    site ∈ allListSites := by
  apply List.mem_filterMap.mpr
  cases site with
  | list0 site =>
      refine ⟨site.site, allGrammarSites_complete site.site, ?_⟩
      simp [listSiteOfGrammarSite?, GrammarSiteOfKind.ofSite?, site.hasKind]
  | list1 site =>
      refine ⟨site.site, allGrammarSites_complete site.site, ?_⟩
      simp [listSiteOfGrammarSite?, GrammarSiteOfKind.ofSite?, site.hasKind]

/-- Every stable production identifier occurs in the displayed production
enumeration. -/
theorem allProductionIds_complete (production : ProductionId) :
    production ∈ allProductionIds := by
  cases production with
  | root rule =>
      simp [allProductionIds, allGrammarRuleIds_complete rule]
  | atom site =>
      simp [allProductionIds, allAtomSites, sitesOfKind_complete site]
  | seq site =>
      simp [allProductionIds, allSequenceSites, sitesOfKind_complete site]
  | group site =>
      simp [allProductionIds, allGroupSites, sitesOfKind_complete site]
  | choice site branch =>
      have member : ProductionId.choice site branch ∈
          allChoiceSites.flatMap fun choiceSite =>
            (List.finRange choiceSite.branchCount).map fun choiceBranch =>
              .choice choiceSite choiceBranch := by
        apply List.mem_flatMap.mpr
        refine ⟨site, sitesOfKind_complete site, ?_⟩
        apply List.mem_map.mpr
        exact ⟨branch, List.mem_finRange branch, rfl⟩
      simp only [allProductionIds, List.mem_append, member,
        or_true, true_or]
  | opt site branch =>
      cases branch <;>
        simp [allProductionIds, allOptionalSites,
          sitesOfKind_complete site]
  | star site branch =>
      cases branch <;>
        simp [allProductionIds, allStarSites, sitesOfKind_complete site]
  | plus site branch =>
      cases branch <;>
        simp [allProductionIds, allPlusSites, sitesOfKind_complete site]
  | list0 site branch =>
      cases branch <;>
        simp [allProductionIds, allList0Sites, sitesOfKind_complete site]
  | list1 site =>
      simp [allProductionIds, allList1Sites, sitesOfKind_complete site]
  | tail site branch =>
      cases branch <;> simp only [allProductionIds, List.mem_append]
      all_goals
        right
        apply List.mem_flatMap.mpr
        exact ⟨site, allListSites_complete site, by simp⟩

/-- The root EBNF sequence site of the source module rule. -/
def moduleRootSequenceSite : SequenceSite := {
  site := GrammarSite.root .module
  hasKind := by
    rw [GrammarSite.root_expression]
    rfl
}

/-- The repeated top-item child of the source module sequence. -/
def moduleItemsGrammarSite : GrammarSite :=
  ⟨{ rule := .module, path := [0] }, by
    unfold GrammarSiteKey.valid m2cV1
    simp [m2cV1Rhs, EbnfExpr.nodeAt?, EbnfExpr.children,
      sequence, star, nonterminal, terminal]⟩

/-- The logical-EOF child of the source module sequence. -/
def moduleEofGrammarSite : GrammarSite :=
  ⟨{ rule := .module, path := [1] }, by
    unfold GrammarSiteKey.valid m2cV1
    simp [m2cV1Rhs, EbnfExpr.nodeAt?, EbnfExpr.children,
      sequence, star, nonterminal, terminal]⟩

/-- The atom refinement of the source module's logical-EOF child. -/
def moduleEofAtomSite : AtomSite := {
  site := moduleEofGrammarSite
  hasKind := by
    unfold moduleEofGrammarSite GrammarSite.expression m2cV1
    simp [m2cV1Rhs, EbnfExpr.nodeAt?, EbnfExpr.kind,
      EbnfExpr.children, sequence, star, nonterminal, terminal]
}

/-- The expanded module sequence has exactly its item-star and EOF children. -/
theorem ProductionId.rhs_moduleRootSequence :
    (ProductionId.seq moduleRootSequenceSite).rhs =
      [.nonterminal (.aux moduleItemsGrammarSite),
        .nonterminal (.aux moduleEofGrammarSite)] := by
  simp [ProductionId.rhs, moduleRootSequenceSite, SequenceSite.children,
    GrammarSite.directChildren, GrammarSite.childAt,
    moduleItemsGrammarSite, moduleEofGrammarSite, GrammarSite.expression,
    GrammarSite.root, GrammarSiteKey.valid, m2cV1, m2cV1Rhs,
    EbnfExpr.nodeAt?, EbnfExpr.children, sequence, nonterminal,
    terminal, List.ofFn, Fin.foldr_succ]

/-- The module EOF atom expands to the one logical-EOF terminal. -/
theorem ProductionId.rhs_moduleEofAtom :
    (ProductionId.atom moduleEofAtomSite).rhs =
      [.terminal .endOfFile] := by
  simp [ProductionId.rhs, moduleEofAtomSite, moduleEofGrammarSite,
    AtomSite.symbol, AtomSite.atom, GrammarSite.expression,
    GrammarSiteKey.valid, m2cV1, m2cV1Rhs, EbnfExpr.nodeAt?,
    EbnfExpr.children, EbnfExpr.atom?, EbnfAtom.grammarSymbol,
    sequence, nonterminal, terminal]

/-- An auxiliary production at the module root site is its exact sequence. -/
theorem ProductionId.eq_moduleRootSequence_of_lhs
    (production : ProductionId)
    (lhs : production.lhs = .aux (GrammarSite.root .module)) :
    production = .seq moduleRootSequenceSite := by
  cases production with
  | root rule => simp [ProductionId.lhs] at lhs
  | atom site =>
      simp only [ProductionId.lhs, NonterminalSymbol.aux.injEq] at lhs
      rcases site with ⟨site, kind⟩
      simp only at lhs
      subst site
      rw [GrammarSite.root_expression] at kind
      contradiction
  | seq site =>
      simp only [ProductionId.lhs, NonterminalSymbol.aux.injEq] at lhs
      rcases site with ⟨site, kind⟩
      simp only at lhs
      subst site
      rfl
  | group site | choice site _ | opt site _ | star site _ | plus site _
      | list0 site _ | list1 site =>
      simp only [ProductionId.lhs, NonterminalSymbol.aux.injEq] at lhs
      rcases site with ⟨site, kind⟩
      simp only at lhs
      subst site
      rw [GrammarSite.root_expression] at kind
      contradiction
  | tail site branch => simp [ProductionId.lhs] at lhs

/-- An auxiliary production at the module EOF site is its exact atom. -/
theorem ProductionId.eq_moduleEofAtom_of_lhs
    (production : ProductionId)
    (lhs : production.lhs = .aux moduleEofGrammarSite) :
    production = .atom moduleEofAtomSite := by
  cases production with
  | root rule => simp [ProductionId.lhs] at lhs
  | atom site =>
      simp only [ProductionId.lhs, NonterminalSymbol.aux.injEq] at lhs
      rcases site with ⟨site, kind⟩
      simp only at lhs
      subst site
      rfl
  | seq site | group site | choice site _ | opt site _ | star site _
      | plus site _ | list0 site _ | list1 site =>
      simp only [ProductionId.lhs, NonterminalSymbol.aux.injEq] at lhs
      rcases site with ⟨site, kind⟩
      simp only at lhs
      subst site
      have atomKind : moduleEofGrammarSite.expression.kind = .atom :=
        moduleEofAtomSite.hasKind
      rw [atomKind] at kind
      contradiction
  | tail site branch => simp [ProductionId.lhs] at lhs

mutual

private def EbnfExpr.containsModuleReference : EbnfExpr → Bool
  | .atom (.nonterminal .module) => true
  | .atom _ => false
  | .sequence children | .choice children =>
      containsModuleReferenceList children
  | .group child | .optional child | .star child | .plus child
      | .list0 child | .list1 child => child.containsModuleReference

private def EbnfExpr.containsModuleReferenceList : List EbnfExpr → Bool
  | [] => false
  | child :: rest =>
      child.containsModuleReference || containsModuleReferenceList rest

end

private theorem EbnfExpr.containsModuleReferenceList_of_mem
    {child : EbnfExpr} : ∀ {children : List EbnfExpr},
    child ∈ children →
    child.containsModuleReference = true →
    EbnfExpr.containsModuleReferenceList children = true := by
  intro children member contains
  induction children with
  | nil => contradiction
  | cons head rest induction =>
      simp only [List.mem_cons] at member
      simp only [EbnfExpr.containsModuleReferenceList, Bool.or_eq_true]
      cases member with
      | inl equal =>
          left
          simpa [equal] using contains
      | inr member =>
          right
          exact induction member

private theorem EbnfExpr.containsModuleReference_child
    {root child : EbnfExpr}
    (member : child ∈ root.children)
    (contains : child.containsModuleReference = true) :
    root.containsModuleReference = true := by
  cases root <;>
    simp [EbnfExpr.children, EbnfExpr.containsModuleReference] at member ⊢
  all_goals
    first
    | exact EbnfExpr.containsModuleReferenceList_of_mem member contains
    | simp_all

private theorem EbnfExpr.containsModuleReference_nodeAt
    (root selected : EbnfExpr) : ∀ path,
    root.nodeAt? path = some selected →
    selected.containsModuleReference = true →
    root.containsModuleReference = true := by
  intro path
  induction path generalizing root with
  | nil =>
      simp only [EbnfExpr.nodeAt?, Option.some.injEq]
      intro equal contains
      subst selected
      exact contains
  | cons index rest induction =>
      simp only [EbnfExpr.nodeAt?]
      cases childEq : root.children[index]? with
      | none => simp
      | some child =>
          simp only
          intro selectedEq contains
          exact EbnfExpr.containsModuleReference_child
            (List.mem_of_getElem? childEq)
            (induction child selectedEq contains)

private theorem m2cV1Rhs_containsModuleReference_false
    (rule : GrammarRuleId) :
    (m2cV1Rhs rule).containsModuleReference = false := by
  cases rule <;> rfl

private theorem AtomSite.symbol_ne_moduleRule (site : AtomSite) :
    site.symbol ≠ .nonterminal (.rule .module) := by
  intro equal
  have atomEq : site.atom = .nonterminal .module := by
    unfold AtomSite.symbol EbnfAtom.grammarSymbol at equal
    cases atom : site.atom <;> simp_all
  have expressionEq : site.site.expression =
      .atom (.nonterminal .module) := by
    rw [AtomSite.expression_eq_atom, atomEq]
  have selected := GrammarSite.selected_eq_some site.site
  have rootContains := EbnfExpr.containsModuleReference_nodeAt
    (m2cV1Rhs site.site.val.rule) site.site.expression site.site.val.path
      selected (by rw [expressionEq]; rfl)
  rw [m2cV1Rhs_containsModuleReference_false] at rootContains
  contradiction

/-- No generated production refers recursively to the source module rule. -/
theorem ProductionId.rhs_no_moduleRule (production : ProductionId) :
    .nonterminal (.rule .module) ∉ production.rhs := by
  cases production with
  | root rule => simp [ProductionId.rhs]
  | atom site =>
      simp only [ProductionId.rhs, List.mem_singleton]
      exact fun equal => AtomSite.symbol_ne_moduleRule site equal.symm
  | seq site => simp [ProductionId.rhs]
  | group site => simp [ProductionId.rhs]
  | choice site branch => simp [ProductionId.rhs]
  | opt site branch => cases branch <;> simp [ProductionId.rhs]
  | star site branch => cases branch <;> simp [ProductionId.rhs]
  | plus site branch => cases branch <;> simp [ProductionId.rhs]
  | list0 site branch => cases branch <;> simp [ProductionId.rhs]
  | list1 site => simp [ProductionId.rhs]
  | tail site branch => cases branch <;> simp [ProductionId.rhs]

private theorem filterMap_nodup_of_functional
    {α β : Type} (parse : α → Option β) (values : List α)
    (unique : values.Nodup)
    (functional : ∀ (left right : α) (result : β),
      parse left = some result → parse right = some result → left = right) :
    (values.filterMap parse).Nodup := by
  rw [List.nodup_iff_pairwise_ne] at unique ⊢
  rw [List.pairwise_filterMap]
  exact unique.imp (fun {left right} different result leftSelected
    other otherSelected equal => by
      subst other
      exact different (functional left right result leftSelected otherSelected))
private def productionGrammarSiteKeysForRule
    (rule : GrammarRuleId) : List GrammarSiteKey :=
  ((m2cV1.rhs rule).sitePaths.map fun path => { rule, path })
private theorem map_nodup_of_injective
    {α β : Type} (function : α → β) (values : List α)
    (unique : values.Nodup)
    (injective : ∀ {left right}, function left = function right →
      left = right) :
    (values.map function).Nodup := by
  rw [List.nodup_iff_pairwise_ne] at unique ⊢
  rw [List.pairwise_map]
  exact unique.imp fun different equal => different (injective equal)
private theorem finRange_nodup (size : Nat) :
    (List.finRange size).Nodup := by
  induction size with
  | zero => simp
  | succ size induction =>
      rw [show List.finRange (size + 1) =
        0 :: (List.finRange size).map Fin.succ from List.finRange_succ]
      rw [List.nodup_cons]
      constructor
      · intro member
        rw [List.mem_map] at member
        rcases member with ⟨value, _, equal⟩
        have valueEqual := congrArg Fin.val equal
        simp at valueEqual
      · exact map_nodup_of_injective Fin.succ _ induction (by
          intro left right equal
          apply Fin.ext
          exact Nat.succ.inj (congrArg Fin.val equal))
private theorem dependentFlatMap_nodup
    {α γ : Type} {β : α → Type}
    (values : List α) (items : (value : α) → List (β value))
    (make : (value : α) → β value → γ)
    (valuesUnique : values.Nodup)
    (itemsUnique : ∀ value, (items value).Nodup)
    (makeInjective : ∀ {left right} {leftItem : β left}
      {rightItem : β right},
      make left leftItem = make right rightItem →
        Sigma.mk left leftItem = Sigma.mk right rightItem) :
    (values.flatMap fun value =>
      (items value).map (make value)).Nodup := by
  induction values with
  | nil => simp
  | cons head tail induction =>
      rw [List.nodup_cons] at valuesUnique
      simp only [List.flatMap_cons]
      rw [List.nodup_append]
      refine ⟨map_nodup_of_injective (make head) _ (itemsUnique head) ?_,
        induction valuesUnique.2, ?_⟩
      · intro left right equal
        exact eq_of_heq (Sigma.ext_iff.mp (makeInjective equal)).2
      · intro left leftMember right rightMember equal
        rw [List.mem_map] at leftMember
        rcases leftMember with ⟨leftItem, _, rfl⟩
        rw [List.mem_flatMap] at rightMember
        rcases rightMember with ⟨owner, ownerMember, rightMember⟩
        rw [List.mem_map] at rightMember
        rcases rightMember with ⟨rightItem, _, rfl⟩
        have ownerEqual := congrArg Sigma.fst (makeInjective equal)
        change head = owner at ownerEqual
        exact valuesUnique.1 (ownerEqual.symm ▸ ownerMember)
private theorem allGrammarSiteKeys_nodup :
    (allGrammarRuleIds.flatMap productionGrammarSiteKeysForRule).Nodup := by
  apply dependentFlatMap_nodup _ _ _
    (by decide) (by intro rule; cases rule <;> decide)
  intro left right leftItem rightItem equal; cases equal; rfl
private theorem allGrammarSites_nodup : allGrammarSites.Nodup := by
  rw [show allGrammarSites =
      (allGrammarRuleIds.flatMap
        productionGrammarSiteKeysForRule).filterMap GrammarSite.ofKey? by
    rfl]
  apply filterMap_nodup_of_functional
    GrammarSite.ofKey? _ allGrammarSiteKeys_nodup
  intro left right result leftSelected rightSelected
  unfold GrammarSite.ofKey? at leftSelected rightSelected
  split at leftSelected <;> split at rightSelected <;> simp_all
  exact congrArg Subtype.val (leftSelected.trans rightSelected.symm)
private theorem sitesOfKind_nodup (kind : EbnfNodeKind) :
    (allGrammarSites.filterMap (GrammarSiteOfKind.ofSite? kind)).Nodup := by
  apply filterMap_nodup_of_functional
    (GrammarSiteOfKind.ofSite? kind) _ allGrammarSites_nodup
  intro left right result leftSelected rightSelected
  unfold GrammarSiteOfKind.ofSite? at leftSelected rightSelected
  split at leftSelected <;> split at rightSelected <;> simp_all
  exact congrArg GrammarSiteOfKind.site
    (leftSelected.trans rightSelected.symm)
private theorem namedSitesOfKind_nodup
    {kind : EbnfNodeKind} (sites : List (GrammarSiteOfKind kind))
    (definition : sites = allGrammarSites.filterMap
      (GrammarSiteOfKind.ofSite? kind)) : sites.Nodup := by
  rw [definition]
  exact sitesOfKind_nodup kind
private def productionListSiteOfGrammarSite? (site : GrammarSite) :
    Option ListSite :=
  match GrammarSiteOfKind.ofSite? .list0 site with
  | some list0Site => some (.list0 list0Site)
  | none =>
      match GrammarSiteOfKind.ofSite? .list1 site with
      | some list1Site => some (.list1 list1Site)
      | none => none
private theorem ofSite?_site
    {kind : EbnfNodeKind} {site : GrammarSite}
    {result : GrammarSiteOfKind kind}
    (selected : GrammarSiteOfKind.ofSite? kind site = some result) :
    result.site = site := by
  unfold GrammarSiteOfKind.ofSite? at selected
  split at selected <;> simp_all
  exact (congrArg GrammarSiteOfKind.site selected).symm
private theorem productionListSiteOfGrammarSite?_owner
    {site : GrammarSite} {result : ListSite}
    (selected : productionListSiteOfGrammarSite? site = some result) :
    result.owner = site := by
  unfold productionListSiteOfGrammarSite? at selected
  cases list0Selected : GrammarSiteOfKind.ofSite? .list0 site with
  | some list0Site =>
      simp only [list0Selected, Option.some.injEq] at selected
      subst result
      exact ofSite?_site list0Selected
  | none =>
      simp only [list0Selected] at selected
      cases list1Selected : GrammarSiteOfKind.ofSite? .list1 site with
      | some list1Site =>
          simp only [list1Selected, Option.some.injEq] at selected
          subst result
          exact ofSite?_site list1Selected
      | none => simp [list1Selected] at selected
private theorem allListSites_nodup : allListSites.Nodup := by
  rw [show allListSites = allGrammarSites.filterMap
      productionListSiteOfGrammarSite? by rfl]
  apply filterMap_nodup_of_functional
    productionListSiteOfGrammarSite? _ allGrammarSites_nodup
  intro left right result leftSelected rightSelected
  exact (productionListSiteOfGrammarSite?_owner leftSelected).symm.trans
    (productionListSiteOfGrammarSite?_owner rightSelected)
private theorem binaryFlatMap_nodup {α β γ : Type} (values : List α)
    (first second : β) (make : α → β → γ) (unique : values.Nodup)
    (itemsUnique : ([first, second] : List β).Nodup)
    (makeInjective : ∀ {a b x y}, make a x = make b y →
      (⟨a, x⟩ : Sigma fun _ : α => β) = ⟨b, y⟩) :
    (values.flatMap fun value => [make value first, make value second]).Nodup :=
  dependentFlatMap_nodup values (fun _ => [first, second]) make
    unique (fun _ => itemsUnique) makeInjective
private def productionTag : ProductionId → Nat
  | .root _ => 0
  | .atom _ => 1
  | .seq _ => 2
  | .group _ => 3
  | .choice _ _ => 4
  | .opt _ _ => 5
  | .star _ _ => 6
  | .plus _ _ => 7
  | .list0 _ _ => 8
  | .list1 _ => 9
  | .tail _ _ => 10
private theorem dependentFlatMap_tagged
    {α γ : Type} {β : α → Type}
    (tag : γ → Nat) (number : Nat) (values : List α)
    (items : (value : α) → List (β value))
    (make : (value : α) → β value → γ)
    (tagMake : ∀ value item, tag (make value item) = number) :
    ∀ output ∈ values.flatMap fun value =>
      (items value).map (make value), tag output = number := by
  intro output member
  rw [List.mem_flatMap] at member
  rcases member with ⟨value, _, member⟩
  rw [List.mem_map] at member
  rcases member with ⟨item, _, rfl⟩
  exact tagMake value item
private theorem append_nodup_of_tag_bound
    (bound : Nat) (left right : List ProductionId)
    (leftUnique : left.Nodup) (rightUnique : right.Nodup)
    (leftBound : ∀ value ∈ left, productionTag value < bound)
    (rightTag : ∀ value ∈ right, productionTag value = bound) :
    (left ++ right).Nodup ∧
      ∀ value ∈ left ++ right, productionTag value < bound + 1 := by
  constructor
  · rw [List.nodup_append]
    refine ⟨leftUnique, rightUnique, ?_⟩
    intro leftValue leftMember rightValue rightMember valueEqual
    have smaller := leftBound leftValue leftMember
    rw [congrArg productionTag valueEqual,
      rightTag rightValue rightMember] at smaller
    exact Nat.lt_irrefl bound smaller
  · intro value member
    rw [List.mem_append] at member
    rcases member with leftMember | rightMember
    · exact Nat.lt_succ_of_lt (leftBound value leftMember)
    · rw [rightTag value rightMember]
      exact Nat.lt_succ_self bound
/-- Stable production IDs occur without duplication. -/
theorem allProductionIds_nodup : allProductionIds.Nodup := by
  have rootUnique : (allGrammarRuleIds.map ProductionId.root).Nodup :=
    map_nodup_of_injective _ _ (by decide)
      (by intro left right equal; cases equal; rfl)
  have atomUnique : (allAtomSites.map ProductionId.atom).Nodup :=
    map_nodup_of_injective _ _ (namedSitesOfKind_nodup allAtomSites rfl)
      (by intro left right equal; cases equal; rfl)
  have sequenceUnique : (allSequenceSites.map ProductionId.seq).Nodup :=
    map_nodup_of_injective _ _
      (namedSitesOfKind_nodup allSequenceSites rfl)
      (by intro left right equal; cases equal; rfl)
  have groupUnique : (allGroupSites.map ProductionId.group).Nodup :=
    map_nodup_of_injective _ _ (namedSitesOfKind_nodup allGroupSites rfl)
      (by intro left right equal; cases equal; rfl)
  have choiceUnique :
      (allChoiceSites.flatMap fun site =>
        (List.finRange site.branchCount).map fun branch =>
          ProductionId.choice site branch).Nodup :=
    dependentFlatMap_nodup _ _ _
      (namedSitesOfKind_nodup allChoiceSites rfl)
      (fun site => finRange_nodup site.branchCount)
      (by intro left right leftItem rightItem equal; cases equal; rfl)
  have optionalUnique :
      (allOptionalSites.flatMap fun site =>
        [ProductionId.opt site .none, ProductionId.opt site .some]).Nodup :=
    binaryFlatMap_nodup _ .none .some ProductionId.opt
      (namedSitesOfKind_nodup allOptionalSites rfl) (by simp)
      (by intro left right leftItem rightItem equal; cases equal; rfl)
  have starUnique :
      (allStarSites.flatMap fun site =>
        [ProductionId.star site .nil, ProductionId.star site .cons]).Nodup :=
    binaryFlatMap_nodup _ .nil .cons ProductionId.star
      (namedSitesOfKind_nodup allStarSites rfl) (by simp)
      (by intro left right leftItem rightItem equal; cases equal; rfl)
  have plusUnique :
      (allPlusSites.flatMap fun site =>
        [ProductionId.plus site .one, ProductionId.plus site .cons]).Nodup :=
    binaryFlatMap_nodup _ .one .cons ProductionId.plus
      (namedSitesOfKind_nodup allPlusSites rfl) (by simp)
      (by intro left right leftItem rightItem equal; cases equal; rfl)
  have list0Unique :
      (allList0Sites.flatMap fun site =>
        [ProductionId.list0 site .nil,
          ProductionId.list0 site .cons]).Nodup :=
    binaryFlatMap_nodup _ .nil .cons ProductionId.list0
      (namedSitesOfKind_nodup allList0Sites rfl) (by simp)
      (by intro left right leftItem rightItem equal; cases equal; rfl)
  have list1Unique : (allList1Sites.map ProductionId.list1).Nodup :=
    map_nodup_of_injective _ _ (namedSitesOfKind_nodup allList1Sites rfl)
      (by intro left right equal; cases equal; rfl)
  have tailUnique :
      (allListSites.flatMap fun site =>
        [ProductionId.tail site .nil, ProductionId.tail site .cons]).Nodup :=
    binaryFlatMap_nodup _ .nil .cons ProductionId.tail
      allListSites_nodup (by simp)
      (by intro left right leftItem rightItem equal; cases equal; rfl)
  have rootBound : ∀ value ∈ allGrammarRuleIds.map ProductionId.root,
      productionTag value < 1 := by simp [productionTag]
  have first := append_nodup_of_tag_bound 1 _ _ rootUnique atomUnique
    rootBound (by simp [productionTag])
  have second := append_nodup_of_tag_bound 2 _ _ first.1 sequenceUnique
    first.2 (by simp [productionTag])
  have third := append_nodup_of_tag_bound 3 _ _ second.1 groupUnique
    second.2 (by simp [productionTag])
  have fourth := append_nodup_of_tag_bound 4 _ _ third.1 choiceUnique
    third.2 (dependentFlatMap_tagged productionTag 4 _ _ _
      (fun _ _ => rfl))
  have fifth := append_nodup_of_tag_bound 5 _ _ fourth.1 optionalUnique
    fourth.2 (dependentFlatMap_tagged productionTag 5 allOptionalSites
      (fun _ => ([.none, .some] : List OptionalBranch))
      ProductionId.opt (fun _ _ => rfl))
  have sixth := append_nodup_of_tag_bound 6 _ _ fifth.1 starUnique
    fifth.2 (dependentFlatMap_tagged productionTag 6 allStarSites
      (fun _ => ([.nil, .cons] : List NilConsBranch))
      ProductionId.star (fun _ _ => rfl))
  have seventh := append_nodup_of_tag_bound 7 _ _ sixth.1 plusUnique
    sixth.2 (dependentFlatMap_tagged productionTag 7 allPlusSites
      (fun _ => ([.one, .cons] : List OneConsBranch))
      ProductionId.plus (fun _ _ => rfl))
  have eighth := append_nodup_of_tag_bound 8 _ _ seventh.1 list0Unique
    seventh.2 (dependentFlatMap_tagged productionTag 8 allList0Sites
      (fun _ => ([.nil, .cons] : List NilConsBranch))
      ProductionId.list0 (fun _ _ => rfl))
  have ninth := append_nodup_of_tag_bound 9 _ _ eighth.1 list1Unique
    eighth.2 (by simp [productionTag])
  have tenth := append_nodup_of_tag_bound 10 _ _ ninth.1 tailUnique
    ninth.2 (dependentFlatMap_tagged productionTag 10 allListSites
      (fun _ => ([.nil, .cons] : List NilConsBranch))
      ProductionId.tail (fun _ _ => rfl))
  exact tenth.1

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

/-- The nullable closure is exact and every repeated element passes the
closed nonnullable-repetition check used by expansion. -/
theorem ebnf_expansion_nonnullable_repetitions :
    nullableGrammarRules = [.optionalComma] ∧
      repetitionsNonnullable = true :=
  ⟨nullableGrammarRules_eq, repetitionsNonnullable_eq_true⟩

/-- The checked m2c-v1 expansion. -/
def expanded : ExpandedGrammar :=
  checkedExpansion.get (by
    simp [checkedExpansion, repetitionsNonnullable_eq_true])

/-- The exact production count derived from `expanded`. -/
def productionCount : Nat :=
  expanded.productionCount

/-- The checked expansion succeeds and is exactly the finite stable-production
enumeration from which its public production count is derived. -/
theorem ebnf_expansion_finite :
    checkedExpansion = some expanded ∧
      expanded.productions =
        allProductionIds.map ExpandedProduction.ofId ∧
      productionCount = allProductionIds.length := by
  have accepted : checkedExpansion = some expanded := by
    have isSome : checkedExpansion.isSome = true := by
      simp [checkedExpansion, repetitionsNonnullable_eq_true]
    apply Option.eq_some_iff_get_eq.mpr
    exact ⟨isSome, by unfold expanded; rfl⟩
  have rows : expanded.productions =
      allProductionIds.map ExpandedProduction.ofId := by
    unfold expanded
    simp [checkedExpansion, repetitionsNonnullable_eq_true]
    rfl
  exact ⟨accepted, rows, by
    simp [productionCount, ExpandedGrammar.productionCount, rows]⟩

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

private theorem enumeration_cardinality
    {α : Type} [BEq α] [LawfulBEq α]
    (values : List α)
    (complete : ∀ value : α, value ∈ values)
    (unique : values.Nodup) :
    ∃ encode : α → Fin values.length,
      Function.Injective encode ∧ Function.Surjective encode := by
  let encode : α → Fin values.length := fun value =>
    ⟨values.idxOf value, List.idxOf_lt_length_of_mem (complete value)⟩
  refine ⟨encode, ?_, ?_⟩
  · intro left right equal
    have leftBound : values.idxOf left < values.length :=
      List.idxOf_lt_length_of_mem (complete left)
    have rightBound : values.idxOf right < values.length :=
      List.idxOf_lt_length_of_mem (complete right)
    have leftSelected : values[values.idxOf left]'leftBound = left := by
      exact beq_iff_eq.mp (List.findIdx_getElem
        (xs := values) (p := (· == left)) (w := leftBound))
    have rightSelected : values[values.idxOf right]'rightBound = right := by
      exact beq_iff_eq.mp (List.findIdx_getElem
        (xs := values) (p := (· == right)) (w := rightBound))
    have sameSelected :
        values[values.idxOf left]'leftBound =
          values[values.idxOf right]'rightBound :=
      congrArg values.get equal
    exact leftSelected.symm.trans (sameSelected.trans rightSelected)
  · intro index
    let value := values[index]
    refine ⟨value, Fin.ext ?_⟩
    change values.idxOf value = index.val
    have valueBound : values.idxOf value < values.length :=
      List.idxOf_lt_length_of_mem (complete value)
    apply (List.getElem?_inj valueBound unique).mp
    rw [List.getElem?_eq_getElem valueBound,
      List.getElem?_eq_getElem index.isLt]
    have selected : values[values.idxOf value]'valueBound = value := by
      exact beq_iff_eq.mp (List.findIdx_getElem
        (xs := values) (p := (· == value)) (w := valueBound))
    simpa [value] using congrArg some selected

private theorem dependentEnumeration_nodup
    {α γ : Type} {β : α → Type}
    (values : List α) (items : (value : α) → List (β value))
    (make : (value : α) → β value → γ)
    (valuesUnique : values.Nodup)
    (itemsUnique : ∀ value, (items value).Nodup)
    (makeInjective : ∀ {left right} {leftItem : β left}
      {rightItem : β right},
      make left leftItem = make right rightItem →
        Sigma.mk left leftItem = Sigma.mk right rightItem) :
    (values.flatMap fun value =>
      (items value).map (make value)).Nodup := by
  induction values with
  | nil => simp
  | cons head tail induction =>
      rw [List.nodup_cons] at valuesUnique
      simp only [List.flatMap_cons]
      rw [List.nodup_append]
      have mappedUnique :
          ((items head).map (make head)).Nodup := by
        rw [List.nodup_iff_pairwise_ne]
        rw [List.pairwise_map]
        exact (itemsUnique head).imp fun different equal =>
          different (eq_of_heq
            (Sigma.ext_iff.mp (makeInjective equal)).2)
      refine ⟨mappedUnique, induction valuesUnique.2, ?_⟩
      intro left leftMember right rightMember equal
      rw [List.mem_map] at leftMember
      rcases leftMember with ⟨leftItem, _, rfl⟩
      rw [List.mem_flatMap] at rightMember
      rcases rightMember with ⟨owner, ownerMember, rightMember⟩
      rw [List.mem_map] at rightMember
      rcases rightMember with ⟨rightItem, _, rfl⟩
      have ownerEqual := congrArg Sigma.fst (makeInjective equal)
      change head = owner at ownerEqual
      exact valuesUnique.1 (ownerEqual.symm ▸ ownerMember)

/-- Every stable dotted RHS in production-table and dot order. -/
def allDottedRhs : List DottedRhs :=
  allProductionIds.flatMap fun production =>
    (List.ofFn fun dot : Fin (production.rhs.length + 1) => dot).map
      fun dot => ({ production, dot } : DottedRhs)

/-- Every dotted RHS occurs in the stable enumeration. -/
theorem allDottedRhs_complete (dotted : DottedRhs) :
    dotted ∈ allDottedRhs := by
  rw [allDottedRhs, List.mem_flatMap]
  refine ⟨dotted.production, allProductionIds_complete _, ?_⟩
  rw [List.mem_map]
  refine ⟨dotted.dot, ?_, rfl⟩
  rw [List.mem_ofFn]
  exact ⟨dotted.dot, rfl⟩

private theorem allDottedRhs_nodup : allDottedRhs.Nodup := by
  apply dependentEnumeration_nodup allProductionIds
    (fun production =>
      List.ofFn fun dot : Fin (production.rhs.length + 1) => dot)
    (fun production dot => ({ production, dot } : DottedRhs))
    allProductionIds_nodup
  · intro production
    rw [List.nodup_iff_pairwise_ne]
    rw [List.pairwise_iff_getElem]
    intro left right _ _ before equal
    simp only [List.getElem_ofFn] at equal
    have sameValue : left = right := congrArg Fin.val equal
    omega
  · intro left right leftDot rightDot equal
    cases equal
    rfl

/-- The dotted RHS enumeration has exactly the displayed dotted count. -/
theorem allDottedRhs_length : allDottedRhs.length = D := by
  rw [allDottedRhs, List.length_flatMap]
  simp only [List.length_map, List.length_ofFn]
  unfold D
  rw [ebnf_expansion_finite.2.1]
  simp only [List.map_map]
  rfl

/-- Exact finite cardinality of stable dotted RHS positions. -/
theorem dottedRhs_cardinality :
    ∃ encode : DottedRhs → Fin D,
      Function.Injective encode ∧ Function.Surjective encode := by
  rw [← allDottedRhs_length]
  exact enumeration_cardinality allDottedRhs
    allDottedRhs_complete allDottedRhs_nodup

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

/-- Stable actions and stable productions form a bijection through the public
constructor and inverse projection. -/
theorem production_action_id_bijective :
    Function.Injective ActionId.actionFor ∧
      Function.Surjective ActionId.actionFor := by
  constructor
  · exact actionFor_injective
  · intro action
    exact ⟨action.production, ActionId.actionFor_production action⟩

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

private def statementChoice : ChoiceSite := {
  site := ⟨{ rule := .statement, path := [] }, by
    unfold GrammarSiteKey.valid m2cV1 m2cV1Rhs EbnfExpr.nodeAt?
    rfl⟩
  hasKind := by
    unfold GrammarSite.expression m2cV1 m2cV1Rhs EbnfExpr.nodeAt?
      EbnfExpr.kind
    rfl
}

private def typeChoice : ChoiceSite := {
  site := ⟨{ rule := .type, path := [] }, by
    unfold GrammarSiteKey.valid m2cV1 m2cV1Rhs EbnfExpr.nodeAt?
    rfl⟩
  hasKind := by
    unfold GrammarSite.expression m2cV1 m2cV1Rhs EbnfExpr.nodeAt?
      EbnfExpr.kind
    rfl
}

private def patternChoice : ChoiceSite := {
  site := ⟨{ rule := .pattern, path := [] }, by
    unfold GrammarSiteKey.valid m2cV1 m2cV1Rhs EbnfExpr.nodeAt?
    rfl⟩
  hasKind := by
    unfold GrammarSite.expression m2cV1 m2cV1Rhs EbnfExpr.nodeAt?
      EbnfExpr.kind
    rfl
}

private def postfixPartChoice : ChoiceSite := {
  site := ⟨{ rule := .postfixPart, path := [] }, by
    unfold GrammarSiteKey.valid m2cV1 m2cV1Rhs EbnfExpr.nodeAt?
    rfl⟩
  hasKind := by
    unfold GrammarSite.expression m2cV1 m2cV1Rhs EbnfExpr.nodeAt?
      EbnfExpr.kind
    rfl
}

private def expressionStatementChoice : ChoiceSite := {
  site := ⟨{ rule := .expressionStatement, path := [] }, by
    unfold GrammarSiteKey.valid m2cV1 m2cV1Rhs EbnfExpr.nodeAt?
    rfl⟩
  hasKind := by
    unfold GrammarSite.expression m2cV1 m2cV1Rhs EbnfExpr.nodeAt?
      EbnfExpr.kind
    rfl
}

set_option linter.unusedSimpArgs false in
private def parameterOptional : OptionalSite := {
  site := ⟨{ rule := .parameter, path := [0] }, by
    simp [GrammarSiteKey.valid, m2cV1, m2cV1Rhs, EbnfExpr.nodeAt?,
      EbnfExpr.children, terminal, hardKeyword, contextualKeyword,
      pragmaName, symbol, category, nonterminal, sequence, choice, group,
      optional, star, plus, list0, list1, identifier, pathComponent]⟩
  hasKind := by
    simp [GrammarSite.expression, m2cV1, m2cV1Rhs, EbnfExpr.nodeAt?,
      EbnfExpr.children, EbnfExpr.kind, terminal, hardKeyword,
      contextualKeyword, pragmaName, symbol, category, nonterminal,
      sequence, choice, group, optional, star, plus, list0, list1,
      identifier, pathComponent]
}

set_option linter.unusedSimpArgs false in
private def letBindingOptional : OptionalSite := {
  site := ⟨{ rule := .letBinding, path := [2, 0, 1] }, by
    simp [GrammarSiteKey.valid, m2cV1, m2cV1Rhs, EbnfExpr.nodeAt?,
      EbnfExpr.children, terminal, hardKeyword, contextualKeyword,
      pragmaName, symbol, category, nonterminal, sequence, choice, group,
      optional, star, plus, list0, list1, identifier, pathComponent]⟩
  hasKind := by
    simp [GrammarSite.expression, m2cV1, m2cV1Rhs, EbnfExpr.nodeAt?,
      EbnfExpr.children, EbnfExpr.kind, terminal, hardKeyword,
      contextualKeyword, pragmaName, symbol, category, nonterminal,
      sequence, choice, group, optional, star, plus, list0, list1,
      identifier, pathComponent]
}

set_option linter.unusedSimpArgs false in
private def atomOptional : OptionalSite := {
  site := ⟨{ rule := .atom, path := [2, 2] }, by
    simp [GrammarSiteKey.valid, m2cV1, m2cV1Rhs, EbnfExpr.nodeAt?,
      EbnfExpr.children, terminal, hardKeyword, contextualKeyword,
      pragmaName, symbol, category, nonterminal, sequence, choice, group,
      optional, star, plus, list0, list1, identifier, pathComponent]⟩
  hasKind := by
    simp [GrammarSite.expression, m2cV1, m2cV1Rhs, EbnfExpr.nodeAt?,
      EbnfExpr.children, EbnfExpr.kind, terminal, hardKeyword,
      contextualKeyword, pragmaName, symbol, category, nonterminal,
      sequence, choice, group, optional, star, plus, list0, list1,
      identifier, pathComponent]
}

set_option linter.unusedSimpArgs false in
private def genericPrefixOptional : OptionalSite := {
  site := ⟨{ rule := .genericPrefix, path := [1] }, by
    simp [GrammarSiteKey.valid, m2cV1, m2cV1Rhs, EbnfExpr.nodeAt?,
      EbnfExpr.children, terminal, hardKeyword, contextualKeyword,
      pragmaName, symbol, category, nonterminal, sequence, choice, group,
      optional, star, plus, list0, list1, identifier, pathComponent]⟩
  hasKind := by
    simp [GrammarSite.expression, m2cV1, m2cV1Rhs, EbnfExpr.nodeAt?,
      EbnfExpr.children, EbnfExpr.kind, terminal, hardKeyword,
      contextualKeyword, pragmaName, symbol, category, nonterminal,
      sequence, choice, group, optional, star, plus, list0, list1,
      identifier, pathComponent]
}

set_option linter.unusedSimpArgs false in
private def matchArmStar : StarSite := {
  site := ⟨{ rule := .matchArm, path := [3] }, by
    simp [GrammarSiteKey.valid, m2cV1, m2cV1Rhs, EbnfExpr.nodeAt?,
      EbnfExpr.children, terminal, hardKeyword, contextualKeyword,
      pragmaName, symbol, category, nonterminal, sequence, choice, group,
      optional, star, plus, list0, list1, identifier, pathComponent]⟩
  hasKind := by
    simp [GrammarSite.expression, m2cV1, m2cV1Rhs, EbnfExpr.nodeAt?,
      EbnfExpr.children, EbnfExpr.kind, terminal, hardKeyword,
      contextualKeyword, pragmaName, symbol, category, nonterminal,
      sequence, choice, group, optional, star, plus, list0, list1,
      identifier, pathComponent]
}

private theorem statementChoice_branchCount :
    statementChoice.branchCount = 11 := by
  unfold statementChoice ChoiceSite.branchCount GrammarSite.expression
    m2cV1 m2cV1Rhs EbnfExpr.nodeAt? EbnfExpr.choiceBranchCount
  rfl

private theorem typeChoice_branchCount : typeChoice.branchCount = 2 := by
  unfold typeChoice ChoiceSite.branchCount GrammarSite.expression
    m2cV1 m2cV1Rhs EbnfExpr.nodeAt? EbnfExpr.choiceBranchCount
  rfl

private theorem patternChoice_branchCount : patternChoice.branchCount = 8 := by
  unfold patternChoice ChoiceSite.branchCount GrammarSite.expression
    m2cV1 m2cV1Rhs EbnfExpr.nodeAt? EbnfExpr.choiceBranchCount
  rfl

private theorem postfixPartChoice_branchCount :
    postfixPartChoice.branchCount = 3 := by
  unfold postfixPartChoice ChoiceSite.branchCount GrammarSite.expression
    m2cV1 m2cV1Rhs EbnfExpr.nodeAt? EbnfExpr.choiceBranchCount
  rfl

private theorem expressionStatementChoice_branchCount :
    expressionStatementChoice.branchCount = 2 := by
  unfold expressionStatementChoice ChoiceSite.branchCount
    GrammarSite.expression m2cV1 m2cV1Rhs EbnfExpr.nodeAt?
    EbnfExpr.choiceBranchCount
  rfl

private def guardedProductions : List ProductionId := [
  .choice statementChoice ⟨3, by rw [statementChoice_branchCount]; omega⟩,
  .choice statementChoice ⟨10, by rw [statementChoice_branchCount]; omega⟩,
  .choice typeChoice ⟨0, by rw [typeChoice_branchCount]; omega⟩,
  .choice typeChoice ⟨1, by rw [typeChoice_branchCount]; omega⟩,
  .choice patternChoice ⟨3, by rw [patternChoice_branchCount]; omega⟩,
  .choice patternChoice ⟨4, by rw [patternChoice_branchCount]; omega⟩,
  .choice postfixPartChoice ⟨0, by rw [postfixPartChoice_branchCount]; omega⟩,
  .choice expressionStatementChoice
    ⟨1, by rw [expressionStatementChoice_branchCount]; omega⟩,
  .opt parameterOptional .none,
  .opt parameterOptional .some,
  .opt letBindingOptional .none,
  .opt letBindingOptional .some,
  .opt atomOptional .none,
  .opt atomOptional .some,
  .opt genericPrefixOptional .none,
  .opt genericPrefixOptional .some,
  .star matchArmStar .nil,
  .star matchArmStar .cons
]

private def guardedKeys : List GuardedProductionKey := [
  .choice .statement [] 3,
  .choice .statement [] 10,
  .choice .type [] 0,
  .choice .type [] 1,
  .choice .pattern [] 3,
  .choice .pattern [] 4,
  .choice .postfixPart [] 0,
  .choice .expressionStatement [] 1,
  .opt .parameter [0] .none,
  .opt .parameter [0] .some,
  .opt .letBinding [2, 0, 1] .none,
  .opt .letBinding [2, 0, 1] .some,
  .opt .atom [2, 2] .none,
  .opt .atom [2, 2] .some,
  .opt .genericPrefix [1] .none,
  .opt .genericPrefix [1] .some,
  .star .matchArm [3] .nil,
  .star .matchArm [3] .cons
]

private theorem guardedProductions_keys :
    guardedProductions.map ProductionId.guardedKey? =
      guardedKeys.map some := by
  rfl

private theorem site_eq_of_fields {kind : EbnfNodeKind}
    (left right : GrammarSiteOfKind kind)
    (ruleEqual : left.site.val.rule = right.site.val.rule)
    (pathEqual : left.site.val.path = right.site.val.path) : left = right := by
  rcases left with ⟨⟨⟨leftRule, leftPath⟩, leftValid⟩, leftKind⟩
  rcases right with ⟨⟨⟨rightRule, rightPath⟩, rightValid⟩, rightKind⟩
  change leftRule = rightRule at ruleEqual
  change leftPath = rightPath at pathEqual
  cases ruleEqual
  cases pathEqual
  rfl

private theorem guardedKey?_injective
    {left right : ProductionId} {key : GuardedProductionKey}
    (leftKey : left.guardedKey? = some key)
    (rightKey : right.guardedKey? = some key) : left = right := by
  have keysEqual : left.guardedKey? = right.guardedKey? :=
    leftKey.trans rightKey.symm
  cases left <;> cases right <;>
    simp [ProductionId.guardedKey?] at leftKey rightKey keysEqual
  case choice.choice leftSite leftBranch rightSite rightBranch =>
    rcases keysEqual with ⟨ruleEqual, pathEqual, branchEqual⟩
    cases site_eq_of_fields leftSite rightSite ruleEqual pathEqual
    cases Fin.ext branchEqual
    rfl
  case opt.opt leftSite leftBranch rightSite rightBranch =>
    rcases keysEqual with ⟨ruleEqual, pathEqual, branchEqual⟩
    cases site_eq_of_fields leftSite rightSite ruleEqual pathEqual
    cases branchEqual
    rfl
  case star.star leftSite leftBranch rightSite rightBranch =>
    rcases keysEqual with ⟨ruleEqual, pathEqual, branchEqual⟩
    cases site_eq_of_fields leftSite rightSite ruleEqual pathEqual
    cases branchEqual
    rfl

private instance : LawfulBEq GrammarRuleId where
  rfl := by
    intro rule
    cases rule <;> decide
  eq_of_beq := by
    intro left right equal
    cases left <;> cases right <;> first | rfl | contradiction

namespace ChoiceSite

/-- The root choice of the source `type` rule has its exact arity. -/
theorem branchCount_eq_two_of_isAt_type
    (site : ChoiceSite)
    (located : site.site.isAt .type [] = true) :
    site.branchCount = 2 := by
  rcases site with ⟨⟨⟨rule, path⟩, valid⟩, hasKind⟩
  simp [GrammarSite.isAt] at located
  rcases located with ⟨rfl, rfl⟩
  unfold ChoiceSite.branchCount GrammarSite.expression m2cV1
    m2cV1Rhs EbnfExpr.nodeAt? EbnfExpr.choiceBranchCount
  rfl

/-- The root choice of the source `postfixPart` rule has its exact arity. -/
theorem branchCount_eq_three_of_isAt_postfixPart
    (site : ChoiceSite)
    (located : site.site.isAt .postfixPart [] = true) :
    site.branchCount = 3 := by
  rcases site with ⟨⟨⟨rule, path⟩, valid⟩, hasKind⟩
  simp [GrammarSite.isAt] at located
  rcases located with ⟨rfl, rfl⟩
  unfold ChoiceSite.branchCount GrammarSite.expression m2cV1
    m2cV1Rhs EbnfExpr.nodeAt? EbnfExpr.choiceBranchCount
  rfl

end ChoiceSite

private def keyMem (key : GuardedProductionKey) :
    List GuardedProductionKey → Bool
  | [] => false
  | head :: tail => if key = head then true else keyMem key tail

private theorem keyMem_eq_true_iff
    (key : GuardedProductionKey) (keys : List GuardedProductionKey) :
    keyMem key keys = true ↔ key ∈ keys := by
  induction keys with
  | nil => simp [keyMem]
  | cons head tail induction => simp [keyMem, induction]

private def guardedKeyIndicator (production : ProductionId) : Nat :=
  match production.guardedKey? with
  | some key => if keyMem key guardedKeys then 1 else 0
  | none => 0

private theorem guardOf_length_eq_indicator (production : ProductionId) :
    (guardOf production).length = guardedKeyIndicator production := by
  cases production <;>
    simp [guardOf, GrammarSite.isAt, guardedKeyIndicator,
      ProductionId.guardedKey?, guardedKeys, keyMem, beq_iff_eq] <;>
    grind (splits := 64)

private theorem production_mem_guardedProductions_iff
    (production : ProductionId) :
    production ∈ guardedProductions ↔
      ∃ key ∈ guardedKeys, production.guardedKey? = some key := by
  constructor
  · intro member
    have mapped : production.guardedKey? ∈
        guardedProductions.map ProductionId.guardedKey? :=
      List.mem_map.mpr ⟨production, member, rfl⟩
    rw [guardedProductions_keys] at mapped
    rcases List.mem_map.mp mapped with ⟨key, keyMember, keyEqual⟩
    exact ⟨key, keyMember, keyEqual.symm⟩
  · rintro ⟨key, keyMember, productionKey⟩
    have mapped : some key ∈ guardedKeys.map some :=
      List.mem_map.mpr ⟨key, keyMember, rfl⟩
    rw [← guardedProductions_keys] at mapped
    rcases List.mem_map.mp mapped with
      ⟨guardedProduction, guardedMember, guardedKey⟩
    have equal := guardedKey?_injective productionKey guardedKey
    exact equal ▸ guardedMember

private theorem guardedKeyIndicator_eq_one_iff (production : ProductionId) :
    guardedKeyIndicator production = 1 ↔
      production ∈ guardedProductions := by
  rw [production_mem_guardedProductions_iff]
  unfold guardedKeyIndicator
  split <;> rename_i selected
  · simp [selected, keyMem_eq_true_iff]
  · simp [selected]

private theorem guardedKeys_nodup : guardedKeys.Nodup := by
  unfold guardedKeys
  decide

private theorem guardedProductions_nodup : guardedProductions.Nodup := by
  have mappedNodup :
      (guardedProductions.map ProductionId.guardedKey?).Nodup := by
    rw [guardedProductions_keys]
    apply List.Pairwise.map some
      (fun left right different equal =>
        different (Option.some.inj equal))
      guardedKeys_nodup
  apply List.Pairwise.of_map ProductionId.guardedKey?
    (fun left right different equal =>
      different (congrArg ProductionId.guardedKey? equal))
    mappedNodup

private theorem nodup_perm_of_mem_iff {alpha : Type}
    (left right : List alpha) (leftNodup : left.Nodup)
    (rightNodup : right.Nodup)
    (sameMembers : ∀ value, value ∈ left ↔ value ∈ right) :
    left.Perm right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons head tail =>
          have impossible : head ∈ ([] : List alpha) :=
            (sameMembers head).mpr (by simp)
          simp at impossible
  | cons head tail induction =>
      rw [List.nodup_cons] at leftNodup
      have headMember : head ∈ right :=
        (sameMembers head).mp (by simp)
      obtain ⟨before, after, rfl⟩ := List.append_of_mem headMember
      have middleNodup : (head :: (before ++ after)).Nodup :=
        rightNodup.perm List.perm_middle
      rw [List.nodup_cons] at middleNodup
      have tailMembers (value : alpha) :
          value ∈ tail ↔ value ∈ before ++ after := by
        constructor
        · intro member
          have inRight := (sameMembers value).mp (by simp [member])
          simp only [List.mem_append, List.mem_cons] at inRight ⊢
          rcases inRight with inBefore | equal | inAfter
          · exact Or.inl inBefore
          · exact (leftNodup.1 (equal ▸ member)).elim
          · exact Or.inr inAfter
        · intro member
          have inRight : value ∈ before ++ head :: after := by
            simp only [List.mem_append, List.mem_cons] at member ⊢
            exact member.elim Or.inl (fun inAfter => Or.inr (Or.inr inAfter))
          rcases List.mem_cons.mp ((sameMembers value).mpr inRight) with
            equal | inTail
          · exact (middleNodup.1 (equal ▸ member)).elim
          · exact inTail
      exact (List.Perm.cons head
        (induction (before ++ after) leftNodup.2 middleNodup.2
          tailMembers)).trans
          List.perm_middle.symm

private def guardedProductionFilter : List ProductionId :=
  allProductionIds.filter fun production =>
    guardedKeyIndicator production == 1

private theorem guardedProductionFilter_perm :
    guardedProductionFilter.Perm guardedProductions := by
  apply nodup_perm_of_mem_iff guardedProductionFilter guardedProductions
  · exact List.Pairwise.filter _ allProductionIds_nodup
  · exact guardedProductions_nodup
  · intro production
    simp only [guardedProductionFilter, List.mem_filter]
    rw [and_iff_right (allProductionIds_complete production)]
    rw [beq_iff_eq]
    exact guardedKeyIndicator_eq_one_iff production

private theorem guardedKeyIndicator_sum_eq_filter_length
    (productions : List ProductionId) :
    (productions.map guardedKeyIndicator).sum =
      (productions.filter fun production =>
        guardedKeyIndicator production == 1).length := by
  induction productions with
  | nil => rfl
  | cons head tail induction =>
      have indicatorCases :
          guardedKeyIndicator head = 0 ∨ guardedKeyIndicator head = 1 := by
        unfold guardedKeyIndicator
        split <;> simp
      rcases indicatorCases with isZero | isOne
      · simp [isZero, induction]
      · simp [isOne, induction, Nat.add_comm]

/-- The exact number of cells in the executable guard table. -/
def H : Nat :=
  (allProductionIds.map fun production => (guardOf production).length).sum

/-- The guard-cell count is unchanged by checked EBNF expansion. -/
theorem H_eq_expanded_guard_table_sum :
    H = (expanded.productions.map fun production =>
      (guardOf production.id).length).sum := by
  unfold H
  rw [ebnf_expansion_finite.2.1, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro production _member
  rfl

/-- The executable grammar guard table has exactly eighteen cells. -/
theorem H_eq_eighteen : H = 18 := by
  calc
    H = (allProductionIds.map guardedKeyIndicator).sum := by
      unfold H
      apply congrArg List.sum
      apply List.map_congr_left
      intro production _member
      exact guardOf_length_eq_indicator production
    _ = guardedProductionFilter.length := by
      exact guardedKeyIndicator_sum_eq_filter_length allProductionIds
    _ = guardedProductions.length :=
      guardedProductionFilter_perm.length_eq
    _ = 18 := rfl

/-- The guards whose structural context start is the prediction origin. -/
def OriginAnchoredGuard (guard : PriorityGuardId) : Prop :=
  guard = .G03_parameterComptime ∨
    guard = .G04_letComptime ∨
    guard = .G05_typeComptime ∨
    guard = .G09_genericContext

/-- Finite static coverage of one expanded nonterminal: a guardless
production, an origin-anchored pair, the postfix pair, or the match-arm pair. -/
inductive StaticNonterminalCoverage
    (symbol : NonterminalSymbol) : Prop where
  | guardless
      (production : ProductionId)
      (lhs : production.lhs = symbol)
      (guards : guardOf production = [])
  | originPair
      (guard : PriorityGuardId)
      (originGuard : OriginAnchoredGuard guard)
      (positive negative : ProductionId)
      (positiveLhs : positive.lhs = symbol)
      (negativeLhs : negative.lhs = symbol)
      (positiveOnly : guardOf positive = [(guard, .positive)])
      (negativeOnly : guardOf negative = [(guard, .negative)])
  | postfixPair
      (positive negative : ProductionId)
      (positiveLhs : positive.lhs = symbol)
      (negativeLhs : negative.lhs = symbol)
      (positiveRule : positive.sourceRule = .atom)
      (negativeRule : negative.sourceRule = .atom)
      (positiveOnly : guardOf positive =
        [(.G07_leadingDotArguments, .positive)])
      (negativeOnly : guardOf negative =
        [(.G07_leadingDotArguments, .negative)])
  | armPair
      (positive negative : ProductionId)
      (positiveLhs : positive.lhs = symbol)
      (negativeLhs : negative.lhs = symbol)
      (positiveRule : positive.sourceRule = .matchArm)
      (negativeRule : negative.sourceRule = .matchArm)
      (positiveOnly : guardOf positive =
        [(.G02_matchArmBoundary, .positive)])
      (negativeOnly : guardOf negative =
        [(.G02_matchArmBoundary, .negative)])

/-- Every expanded nonterminal has one of the finite static coverage forms. -/
theorem staticNonterminalCoverage
    (symbol : NonterminalSymbol) :
    StaticNonterminalCoverage symbol := by
  cases symbol with
  | rule rule =>
      exact .guardless (.root rule) rfl (by simp [guardOf])
  | tail site =>
      exact .guardless (.tail site .nil) rfl (by simp [guardOf])
  | aux site =>
      cases expression : site.expression with
      | atom atom =>
          let atomSite : AtomSite := ⟨site, by
            simp [expression, EbnfExpr.kind]⟩
          exact .guardless (.atom atomSite) rfl (by simp [guardOf])
      | sequence children =>
          let sequenceSite : SequenceSite := ⟨site, by
            simp [expression, EbnfExpr.kind]⟩
          exact .guardless (.seq sequenceSite) rfl (by simp [guardOf])
      | group child =>
          let groupSite : GroupSite := ⟨site, by
            simp [expression, EbnfExpr.kind]⟩
          exact .guardless (.group groupSite) rfl (by simp [guardOf])
      | choice branches =>
          let choiceSite : ChoiceSite := ⟨site, by
            simp [expression, EbnfExpr.kind]⟩
          by_cases typeLocated : site.isAt .type [] = true
          · have count := ChoiceSite.branchCount_eq_two_of_isAt_type
              choiceSite typeLocated
            let positive : Fin choiceSite.branchCount := ⟨0, by omega⟩
            let negative : Fin choiceSite.branchCount := ⟨1, by omega⟩
            refine .originPair .G05_typeComptime
              (Or.inr (Or.inr (Or.inl rfl)))
              (.choice choiceSite positive) (.choice choiceSite negative)
              rfl rfl ?_ ?_
            · simp [guardOf, choiceSite, typeLocated, positive]
            · simp [guardOf, choiceSite, typeLocated, negative]
          · by_cases postfixLocated :
                site.isAt .postfixPart [] = true
            · have count :=
                ChoiceSite.branchCount_eq_three_of_isAt_postfixPart
                  choiceSite postfixLocated
              let branch : Fin choiceSite.branchCount := ⟨2, by omega⟩
              exact .guardless (.choice choiceSite branch) rfl
                (by simp [guardOf, choiceSite, branch])
            · let branch : Fin choiceSite.branchCount :=
                ⟨0, ChoiceSite.branchCount_pos choiceSite⟩
              exact .guardless (.choice choiceSite branch) rfl
                (by simp [guardOf, choiceSite, typeLocated,
                  postfixLocated, branch])
      | optional child =>
          let optionalSite : OptionalSite := ⟨site, by
            simp [expression, EbnfExpr.kind]⟩
          by_cases parameterLocated : site.isAt .parameter [0] = true
          · refine .originPair .G03_parameterComptime (Or.inl rfl)
              (.opt optionalSite .some) (.opt optionalSite .none)
              rfl rfl ?_ ?_
            · simp [guardOf, optionalSite, parameterLocated]
            · simp [guardOf, optionalSite, parameterLocated]
          · by_cases letLocated :
                site.isAt .letBinding [2, 0, 1] = true
            · refine .originPair .G04_letComptime
                (Or.inr (Or.inl rfl))
                (.opt optionalSite .some) (.opt optionalSite .none)
                rfl rfl ?_ ?_
              · simp [guardOf, optionalSite, parameterLocated, letLocated]
              · simp [guardOf, optionalSite, parameterLocated, letLocated]
            · by_cases atomLocated : site.isAt .atom [2, 2] = true
              · have atomRule : site.val.rule = .atom :=
                  (by
                    have located :
                        (site.val.rule == .atom) = true ∧
                          (site.val.path == [2, 2]) = true := by
                      simpa [GrammarSite.isAt] using atomLocated
                    exact beq_iff_eq.mp located.1)
                refine .postfixPair
                  (.opt optionalSite .some) (.opt optionalSite .none)
                  rfl rfl (by simpa [ProductionId.sourceRule, optionalSite])
                  (by simpa [ProductionId.sourceRule, optionalSite])
                  ?_ ?_
                · simp [guardOf, optionalSite, parameterLocated, letLocated,
                    atomLocated]
                · simp [guardOf, optionalSite, parameterLocated, letLocated,
                    atomLocated]
              · by_cases genericLocated :
                    site.isAt .genericPrefix [1] = true
                · refine .originPair .G09_genericContext
                    (Or.inr (Or.inr (Or.inr rfl)))
                    (.opt optionalSite .some) (.opt optionalSite .none)
                    rfl rfl ?_ ?_
                  · simp [guardOf, optionalSite, parameterLocated, letLocated,
                      atomLocated, genericLocated]
                  · simp [guardOf, optionalSite, parameterLocated, letLocated,
                      atomLocated, genericLocated]
                · exact .guardless (.opt optionalSite .none) rfl
                    (by simp [guardOf, optionalSite, parameterLocated, letLocated,
                      atomLocated, genericLocated])
      | star child =>
          let starSite : StarSite := ⟨site, by
            simp [expression, EbnfExpr.kind]⟩
          by_cases matchArmLocated : site.isAt .matchArm [3] = true
          · have matchArmRule : site.val.rule = .matchArm :=
              (by
                have located :
                    (site.val.rule == .matchArm) = true ∧
                      (site.val.path == [3]) = true := by
                  simpa [GrammarSite.isAt] using matchArmLocated
                exact beq_iff_eq.mp located.1)
            refine .armPair (.star starSite .nil) (.star starSite .cons)
              rfl rfl (by simpa [ProductionId.sourceRule, starSite])
              (by simpa [ProductionId.sourceRule, starSite]) ?_ ?_
            · simp [guardOf, starSite, matchArmLocated]
            · simp [guardOf, starSite, matchArmLocated]
          · exact .guardless (.star starSite .nil) rfl
              (by simp [guardOf, starSite, matchArmLocated])
      | plus child =>
          let plusSite : PlusSite := ⟨site, by
            simp [expression, EbnfExpr.kind]⟩
          exact .guardless (.plus plusSite .one) rfl (by simp [guardOf])
      | list0 child =>
          let listSite : List0Site := ⟨site, by
            simp [expression, EbnfExpr.kind]⟩
          exact .guardless (.list0 listSite .nil) rfl (by simp [guardOf])
      | list1 child =>
          let listSite : List1Site := ⟨site, by
            simp [expression, EbnfExpr.kind]⟩
          exact .guardless (.list1 listSite) rfl (by simp [guardOf])

end Solcore.Surface.Multi.Grammar
