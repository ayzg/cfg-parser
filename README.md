# Context Free Grammar Parser
## Brief
Usage:
``` bash
    cfg-parser <path_to_cfg_file>
```
CFG(Context Free Grammar) parser cli app. Parses a CFG into an IR. From the IR you can:
- Add Production 
- Transform to Chomsky Normal Form Start.
- Transform to Chomsky Normal Form Term.
- Transform to Chomsky Normal Form BIN.
- Apply Chomsky Normal Form Unit Transform.

Many available CFG parser use a slightly altered syntax. 
This parser stays true to the standard EBNF grammar of the CFG notation.
See `tests/basic_expr.txt` and `cand.cfg` for example CFG files.

## Purpose
I made this to validate the CFG of the C& programming language for the **C& Compiler**'s parser.

There are many great online CFG parsers, but due to the fact that they are online - tend to bug out with large inputs.
Specifically a full(complex) language's cfg will generate titanic LR tables that crash the website.

When designing a language at the start its easy to prototype a simple parser. Once you get to handling the operators
including precedence,associativity and operation a proper CFG and EBNF grammar is reccomended for reference.
Its not possible to wholly respresent a non context free language with, CFG but it allows you to break down
the language into peices and reference them when implementing the parser without second guessing the outcome.

This was speed-coded in a 2 days as I was deep into the C& parser and studying automata theory at the time.
Not sure if there are any edge cases that arent handled but it works.

## Details

**EBNF notation for a context free grammar's grammar.**
``` ebnf
<syntax> ::= <rule_decl>*

<rule_decl> ::= <nonterminal> <opt_blank> <RIGHT_ARROW> <opt_blank> <or> <opt_blank> <FULL_STOP> <opt_blank> <opt_newline> 

<alternative> ::= <op_set> <opt_blank> (<VERTICAL_LINE> <opt_blank> <alternative>)* 
<alternative> ::= <LEFT_PARENTHESIS> <opt_blank> <alternative> <opt_blank> <RIGHT_PARENTHESIS> 
<alternative> ::= <op_set> 

<op_set> ::= ( <terminal> <opt_blank> | <nonterminal> <opt_blank> )* 

<nonterminal> ::= <KW_E> | <IDENTIFIER> 

<terminal> ::= <STRING_LITERAL> 

<opt_blank> ::= <WHITESPACE>*

<opt_newline> ::= <NEWLINE>*

<KW_E> ::= "E"

<RIGHT_ARROW> ::= <HYPHEN_MINUS> <GREATER_THAN_SIGN>
```

**Chomsky Normal Form : Start**
```
Assert the special syntax rule 'S' exists.
Add new start symbol: S0 → S
```

**Chomsky Normal Form : Term**
```
Expand rules with non-solitary terminals:
   RULE -> NON-TERM(0) NON-TERM(TERM-1) TERM NONTERM(TERM+1) NONTERM(N)
For each first occurence of TERM create new rule:
   NS[N] -> TERM
Replace all TERMs with a matching NS[N] inside the current rule.
```

**Chomsky Normal Form : BIN**
```
Expand right hand sides with more than 2 non-terminals
@note after the first step all left-hand-sides should be only
non-terminals, or a single terminal, E or S
  R -> [non-term](i) [non-term](i+1)... [non-term](i+N)
Create new rules for i = 0 to (n-2) :
  @R[i] -> [[non-term][i]] @R[i+1]
  @R[i+1] -> [[non-term][i]] @R[i+2]
  ...
  @R[i+[n-2]] -> [[non-term][n-1]] @R[n]
```

**Apply Chomsky Normal Form Unit Transform**
```
Replace all unit rules with their right hand side definition:
  R -> [non-term]
For each alternative rule of [non-term] add a new rule inlining the
alternative definition:
  [[R]_[non-term]_[i]] -> [[op-set][i]] for [i + N] in [R...]
```

