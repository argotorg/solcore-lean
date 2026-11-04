import Solcore.Syntax.Parser.PublicOutputs
import Solcore.Syntax.Parser.Internal.DiagnosticTrace
import Solcore.Syntax.Parser.Internal.SourceFileTrace
import Solcore.Syntax.Parser.Internal.TypeTrace
import Solcore.Syntax.Internal.NameTrace
import Solcore.Syntax.Internal.PragmaTrace
import Solcore.Syntax.Internal.BlockTrace
import Solcore.Syntax.Parser.Internal.BlockTrace
import Solcore.Syntax.Parser.Internal.LambdaTrace
import Solcore.Syntax.Parser.Internal.ExpressionAtomTrace
import Solcore.Syntax.Internal.DelimitedTrace
import Solcore.Syntax.Parser.Internal.DelimitedTrace
import Solcore.Syntax.Internal.ExpressionTrace
import Solcore.Syntax.Parser.Internal.ParenthesizedTrace
import Solcore.Syntax.Internal.DotConstructorTrace
import Solcore.Syntax.Internal.TypeTrace
import Solcore.Syntax.Internal.ParameterTrace
import Solcore.Syntax.Parser.Internal.ParameterTrace
import Solcore.Syntax.Parser.Internal.ParameterListTrace
import Solcore.Syntax.Grammar.Expressions
import Solcore.Syntax.Internal.ExpressionOutcomes
import Solcore.Syntax.Parser.Internal.PostfixTrace
import Solcore.Syntax.Parser.Internal.DelimitedTotality
import Solcore.Syntax.Parser.Internal.ExpressionTotality

/-!
A summary of the diagnostic-trace results, and the import that gathers them. The module
doc below says what each layer proves.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.SyntaxDiagnosticTraceProperties
/-! Exact primitive, pragma success/rejection, and recovery traces with independent
mixed-report filtering. Complete public slices cover empty tokens, one top-item
recovery, arbitrary successful pragma sequences, and successful pragma prefixes
ending at recognized rejection. Sequencing, transactional choice, and balanced
isolation have compositional execution laws. Independent isolation traces lift
explicit inner trace contracts. Raw and isolated Core blocks have full trace
correspondence under statement contracts. Concrete break/continue leaves have
unconditional exact traces. Return traces compose explicit expression contracts.
Literal/Boolean primitives and literal/identifier-expression leaves have exact traces;
Raw block statements inherit exact traces under inner statement contracts;
protected earlier events compose through successful and rejected raw statements;
generic no-trailing lists have exact success/rejection traces under child contracts;
array literals inherit five expression contracts and exact AST mapping;
leading-dot constructors preserve Boolean-first name events before argument traces;
parenthesized groups/tuples have conditional exact traces with silent closes and
right-paren-only reports after non-comma successful children;
proxy expressions retain nested type events and exact raw failures under type contracts;
named-type finishing unconditionally records bare-mapping constraint events;
optional lambda return annotations lift real type outcomes and bypass absent arrows;
qualified names unconditionally retain checked components and full success/rejection states;
trailing-enabled lists preserve comma-first and immediate-close priority under child contracts;
optional named-type arguments inherit exact nonempty-list outcomes and silent absence;
raw named types compose name, argument, and finishing events without dispatch assumptions;
raw mapping types retain exact key/value events and all six first-failure positions;
raw proxy types forward nested type outcomes with no extra success/rejection frame premise;
raw comptime types retain the nested event suffix and all four first-failure positions;
raw tuple types retain every element, including empty and singleton lists;
optional function returns preserve silent absence and exact trailing-list outcomes;
raw function types retain exact parameter-before-return events and complete component states;
all recursive type successes unconditionally preserve source and full active window;
one type-dispatch layer preserves all prioritized guards and exact outcomes under child trace contracts;
child-relation implication lifts through lists, raw types, and dispatch without altering any traced data;
both trace soundness laws plus independent exactness and explicit invariant exclusion yield completeness;
recursive type successes and rejections have unconditional fuel-free traces with protected events;
independent recursive type outcomes are unique and disjoint, with unconditional production trace completeness;
separate totality and soundness supply an actual traced outcome on every state and independent remainder;
recursive type traces reconstruct every field of successful and rejected states;
proxy expressions and optional lambda returns instantiate concrete unrestricted type contracts;
typed and error parameter finishers retain exact values and append only their own constraint events;
named parameter tails have unconditional five contracts, whole-State equivalences, and ordered type/finishing events;
ordinary name checks preserve exact prefix events, while both parameter dispatchers select the same window-visible pair;
raw named parameters and their selected non-recovering core have unconditional exact traces and whole-State correspondence;
separate core totality and soundness give non-vacuous traced outcome existence on arbitrary inputs;
lambda parameter tails retag exact typed outcomes and distinguish inferred absence from comptime errors;
standalone parameter recovery has exact full-State traces with conditional recovery-event filtering;
public named parameters compose cursor-only rewind, one report commitment, and exact recovery outcomes;
raw lambda parameters and their pair-selected core preserve exact inferred/typed/error outcomes and complete traces;
standalone lambda recovery preserves function-recovery states and events while retagging only the error AST;
public lambda parameters have exact rewind/recovery traces, whole-State equivalences, and separate outcome existence;
actual function and inline lambda parameter lists inherit unconditional exact traces and separate outcome existence;
raw lambda expressions compose concrete parameters and returns with explicit body trace contracts and conditional filters;
expression-atom guards independently select one of eight raw branches on arbitrary token remainders;
standalone atom recovery preserves exact error ASTs and singleton events, with conditional lexical filtering;
one selected atom-core layer has exact raw trace correspondence under explicit nested-expression and body contracts;
separate rejection frames preserve a chosen window observation, including end-byte-only frames that allow end-index changes;
public atoms compose abstract core traces with exact cursor-only rewind and recovery under explicit source/end-byte frames;
the concrete selected-core/public layer composes recursive child contracts, with separate bounded totality and trace existence;
maximal postfix tails have independent exact prioritized traces and all-fuel ordinary-outcome soundness under child contracts;
postfix derivations execute above their own thresholds, while explicit progress/budgets separately give production totality and trace existence;
pointwise postfix correspondences reconstruct complete States with explicit rejected source/end-byte frames;
actual atom-plus-postfix composition preserves ordered traces and pointwise complete States under explicit atom/nested contracts;
separate bounded composition totality and trace existence still require an atom endpoint budget or a supplied atom contract;
atom ordinary execution also accepts bounded body contracts, and one concrete atom/postfix layer retains explicit child frames;
numeric-only success/rejection frames compose through recovery, constructing an atom fuel contract from two bounded children;
actual postfix contracts now construct the intermediate atom internally, and child-only bounded soundness supplies layer trace existence;
unary prefixes have unconditional silent full-State scanning and existence; corresponding postfix contracts lift independently through unary traces;
unary layers inherit postfix numeric fuel contracts without adding fuel, with separately proved bounded trace existence;
general expressions and remaining statement traces remain open. -/
end
