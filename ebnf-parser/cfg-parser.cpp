// langdev.cpp : This file contains the 'main' function. Program execution
// begins and ends there.
//

#include <cassert>
#include <expected>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <map>
#include <set>
#include <source_location>
#include <span>
#include <string_view>
#include <vector>

#ifdef _DEBUG
#define DBGEXCEPT(expression, msg)                                    \
  if ((!!!(expression))) {                                            \
    throw(string(#expression "|" msg "\n[") +                         \
          std::source_location::current().file_name() + "]" + "\n[" + \
          std::source_location::current().function_name() + "]");     \
  }
#else
#define DBGEXCEPT(expression, msg)
#endif

namespace cfg {
// clang-format off
// EBNF notation for a context free grammar's grammar.
/*

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

*/
// clang-format on
using std::expected;
using std::format;
using std::span;
using std::string;
using std::string_view;
using std::unexpected;
using std::vector;

// Grammar rule/production type.
// prefix [kt] = terminal
// prefix [ki] = non-terminal
enum class eProduction : std::size_t {
  ktIdentifier,
  ktStringLiteral,
  ktRightArrow,
  ktLeftParen,
  ktRightParen,
  ktVerticalLine,
  ktFullStop,
  ktNewline,
  ktWhitespace,

  kiSyntax,
  kiOpSet,
  kiAlternative,
  kiRuleDecl,
};

string_view eProductionToCStr(eProduction e) {
  using enum eProduction;
  switch (e) {
    case ktIdentifier:
      return "ktIdentifier";
    case ktStringLiteral:
      return "ktStringLiteral";
    case ktRightArrow:
      return "ktRightArrow";
    case ktLeftParen:
      return "ktLeftParen";
    case ktRightParen:
      return "ktRightParen";
    case ktVerticalLine:
      return "ktVerticalLine";
    case ktFullStop:
      return "ktFullStop";
    case ktNewline:
      return "ktNewline";
    case ktWhitespace:
      return "ktWhitespace";
    case kiSyntax:
      return "kiSyntax";
    case kiOpSet:
      return "kiOpSet";
    case kiAlternative:
      return "kiAlternative";
    case kiRuleDecl:
      return "kiRuleDecl";
    default:
      return "??UNKNOWN??";
  }
}

struct Tk {
  eProduction type;
  string_view literal;
};

struct Ast {
  eProduction type;
  string literal;
  vector<Ast> branches;
};

class IR {
  std::set<string, std::less<>> productions;
  std::multimap<string, Ast, std::less<>> rules;

 public:
  expected<void, string> AddProduction(const Ast& rule) {
    DBGEXCEPT(rule.type == eProduction::kiRuleDecl,
              "[IR] Expected kiRuleDecl ast type.");
    DBGEXCEPT(!rule.branches.empty() ||
                  rule.branches.at(0).type == eProduction::ktIdentifier,
              "[IR] Expected ktIdentifier as first branch of kiRuleDecl.");
    DBGEXCEPT(rule.branches.size() >= 2,
              "[IR] Expected a rule definition operand set.");

    if (!productions.contains(rule.branches.at(0).literal))
      productions.insert(rule.branches.at(0).literal);
    auto& def = rule.branches.at(1);
    for (auto& alt : def.branches)  // Separate each alterantive rule.
      rules.insert({rule.branches.at(0).literal, alt});
    return expected<void, string>{};
  }

  expected<void, string> AddRule(string_view name, const Ast& opset) {
    DBGEXCEPT(opset.type == eProduction::kiOpSet,
              "[IR] Expected kiOpSet ast type.");
    DBGEXCEPT(opset.branches.size() >= 1,
              "[IR] Expected a rule definition operand set.");
    if (!productions.contains(name)) productions.emplace(name);
    rules.emplace(name, opset);
    return expected<void, string>{};
  }

  expected<void, string> ChomskyNormalFormStart() {
    // Assert the special syntax rule 'S' exists.
    if (!productions.contains("S"))
      return unexpected(
          "[IR] CFG Rule 'S' must be defined before converting to Chomsky "
          "normal form.");

    // Add new start symbol: S0 → S
    productions.emplace("R");
    rules.insert(
        {"R",
         Ast{eProduction::kiOpSet, "", {Ast{eProduction::ktIdentifier, "S"}}}});
    return expected<void, string>{};
  }

  // Expand rules with non-solitary terminals:
  //    RULE -> NON-TERM(0) NON-TERM(TERM-1) TERM NONTERM(TERM+1) NONTERM(N)
  // For each first occurence of TERM create new rule:
  //    NS[N] -> TERM
  // Replace all TERMs with a matching NS[N] inside the current rule.
  expected<void, string> ChomskyNormalFormTerm() {
    using enum eProduction;
    std::size_t nsrule_count{0};
    for (auto& prod : productions) {
      auto [beg, end] = rules.equal_range(prod);
      for (auto& [name, rule] : std::ranges::subrange(beg, end)) {
        // Cant be nonsolitary if only 1 op
        auto& opset = rule.branches;
        if (!(opset.size() == 1)) {
          bool has_nonterm{false};
          for (const auto& term : opset)
            if (term.type == ktIdentifier) has_nonterm = true;

          // Create new rule @term1 - @term[n] for each terminal in the rule.
          // Replace that terminal with the new non-terminal production.
          if (has_nonterm)
            for (auto& term : opset) {
              if (term.type == ktStringLiteral) {
                auto new_name = std::format("NS{}", nsrule_count);
                AddRule(new_name,
                        Ast{kiOpSet, "", {{ktStringLiteral, term.literal}}});
                term.type = ktIdentifier;
                term.literal = new_name;
                nsrule_count++;
              }
            }
        }
      }
    }
    return expected<void, string>{};
  }

  // Expand right hand sides with more than 2 non-terminals
  // @note after the first step all left-hand-sides should be only
  // non-terminals, or a single terminal, E or S
  //    R -> [non-term](i) [non-term](i+1)... [non-term](i+N)
  // Create new rules for i = 0 to (n-2) :
  //    @R[i] -> [[non-term][i]] @R[i+1]
  //    @R[i+1] -> [[non-term][i]] @R[i+2]
  //    ...
  //    @R[i+[n-2]] -> [[non-term][n-1]] @R[n]
  expected<void, string> ChomskyNormalFormBIN() {
    using enum eProduction;
    using std::make_pair;
    using std::next;
    using std::size_t;
    using std::ranges::subrange;

    // For each existing production...
    for (auto& prod : productions) {
      const auto& [beg, end] = rules.equal_range(prod);

      size_t bin_offset{0};
      // For each alternative rule of the production... expand
      for (auto alt_it = beg; alt_it != end; alt_it++) {
        const auto& [name, rule] = *alt_it;
        if (rule.branches.size() <= 2)
          continue;  // Skip rules with 2 or less ops
        size_t bin_count{0};
        for (auto [i_0, i_n] = make_pair(rule.branches.cbegin(),
                                         next(rule.branches.cbegin()));
             i_n != rule.branches.cend(); [&] {
               i_0++;
               i_n++;
               bin_count++;
             }()) {
          auto new_name = format(
              "@{}{}{}", name,
              bin_offset == 0 && bin_count == 0 ? "" : format("_{}", bin_count),
              bin_offset == 0 && bin_count == 0 ? ""
                                                : format("_{}", bin_offset));
          AddRule(format("@{}{}{}", name,
                         bin_offset == 0 && bin_count == 0
                             ? ""
                             : format("_{}", bin_count),
                         bin_offset == 0 && bin_count == 0
                             ? ""
                             : format("_{}", bin_offset)),
                  {kiOpSet, "", {*i_0, *i_n}});
        }
        bin_offset++;
      }

      // Erase all expanded alternatives for this production
      std::erase_if(
          rules,
          [&prod](
              const std::multimap<string, Ast, std::less<>>::value_type& e) {
            return (e.first == prod && e.second.branches.size() > 2);
          });
    }

    return expected<void, string>{};
  }

  // Replace all unit rules with their right hand side definition:
  //    R -> [non-term]
  // For each alternative rule of [non-term] add a new rule inlining the
  // alternative definition:
  //    [[R]_[non-term]_[i]] -> [[op-set][i]] for [i + N] in [R...]
  expected<void, string> ApplyCnfUnitTransform() {
    using enum eProduction;
    using std::make_pair;
    using std::next;
    using std::size_t;
    using std::ranges::subrange;
    for (auto& prod : productions) {
      const auto& [beg, end] = rules.equal_range(prod);
      for (const auto& [rule_name, rule] : subrange(beg, end)) {
        if (rule.branches.size() > 1) continue;

        if (rule.branches.at(0).type == ktStringLiteral ||
            rule.branches.at(0).literal == "E" ||
            rule.branches.at(0).literal == "R")
          continue;

        // Find the right hand side non-term rules.
        const auto& [expand_beg, expand_end] =
            rules.equal_range(rule.branches.at(0).literal);

        // Create a new rule for each non-term alternative rule.
        size_t newrule_count{0};
        for (const auto& [rhs_name, rhs_rule] :
             subrange(expand_beg, expand_end)) {
          AddRule(format("@{}{}", rule_name,
                         newrule_count == 0 ? "" : format("{}", newrule_count)),
                  rhs_rule);
          newrule_count++;
        }
      }

      // Erase if:
      // - Production name , size is 1 , rhs is a non-term except 'R', 'E' or 'S'
      std::erase_if(
          rules,
          [&prod](
              const std::multimap<string, Ast, std::less<>>::value_type& e) {
            return (e.first == prod) && (e.second.branches.size() == 1) &&
                   (e.second.branches.at(0).type != ktStringLiteral) &&
                   (e.second.branches.at(0).literal != "R") &&
                   (e.second.branches.at(0).literal != "E") &&
                   (e.second.branches.at(0).literal != "S");
          });
    }

    return expected<void, string>{};
  }

  std::string Format() {
    std::string ret{""};
    int prod_count = 0;
    int prod_alt_count = 0;
    for (auto& prod : productions) {
      auto [beg, end] = rules.equal_range(prod);
      for (const auto& [name, alt] : std::ranges::subrange(beg, end)) {
        string opset{""};
        for (const auto& op : alt.branches) {
          opset += " " + op.literal;
        }
        ret += std::format("{} -> {}\n", prod, opset);
        prod_alt_count++;
      }
      prod_alt_count = 0;
      prod_count++;
    }
    return ret;
  }
};

// Result of an intermediate parsing automaton.
struct ParseResult {
  Ast ast;
  span<Tk>::const_iterator head;
};

// Result of an intermediate lexing automaton.
struct LexResult {
  Tk tk;
  string_view head;
};

using ExTk = std::expected<vector<Tk>, string>;
using ExAst = std::expected<Ast, string>;
using ExParseResult = std::expected<ParseResult, string>;
using ExLexResult = std::expected<LexResult, string>;
using FailResult = std::unexpected<string>;
using TkSpanIter = span<Tk>::const_iterator;

ExTk Lex(string_view s) noexcept;
ExLexResult LexIdentifier(string_view s) noexcept;
ExLexResult LexWhitespace(string_view s) noexcept;
ExLexResult LexNewline(string_view s) noexcept;
ExLexResult LexEscapedCharSequence(string_view s) noexcept;

ExAst Parse(span<Tk> in) noexcept;
void SkipIgnored(TkSpanIter& it, const TkSpanIter& end) noexcept;
ExParseResult ParseOperand(TkSpanIter it, TkSpanIter end) noexcept;
ExParseResult ParseOperandSet(TkSpanIter it, TkSpanIter end) noexcept;
ExParseResult ParseAlternative(TkSpanIter it, TkSpanIter end) noexcept;
ExParseResult ParseSubAlternative(TkSpanIter it, TkSpanIter end) noexcept;
ExParseResult ParseRuleDecl(TkSpanIter it, TkSpanIter end) noexcept;

std::string FormatAst(const Ast& ast, std::size_t depth = 0) {
  std::string ret{""};
  ret += std::format("[{}{}]", eProductionToCStr(ast.type),
                     ast.literal.empty() ? "" : ", " + ast.literal);
  for (const auto& branch : ast.branches) {
    ret += "\n";
    for (int i = 0; i < depth; i++) {
      ret += "    ";
    }
    ret += FormatAst(branch, depth + 1);
  }
  return ret;
}

ExTk Lex(string_view s) noexcept {
  if (s.empty()) return FailResult("Cannot lex empty source.");
  vector<Tk> tokens;
  while (s != "") {
    if (s[0] == '\n') {
      auto res_buff = LexNewline(s);
      if (!res_buff) return FailResult{res_buff.error()};
      tokens.push_back(res_buff->tk);
      s = res_buff->head;
    } else if (s[0] == ' ' || s[0] == '\t') {
      auto res_buff = LexWhitespace(s);
      if (!res_buff) return FailResult{res_buff.error()};
      tokens.push_back(res_buff->tk);
      s = res_buff->head;
    } else if (std::isalpha(s[0]) || s[0] == '_' || s[0] == '$') {
      auto res_buff = LexIdentifier(s);
      if (!res_buff) return FailResult{res_buff.error()};
      tokens.push_back(res_buff->tk);
      s = res_buff->head;
    } else if (s[0] == '"') {
      auto res_buff = LexEscapedCharSequence(s);
      if (!res_buff) return FailResult{res_buff.error()};
      tokens.push_back(res_buff->tk);
      s = res_buff->head;
    } else if (s[0] == '.') {
      tokens.emplace_back(eProduction::ktFullStop);
      s = s.substr(1);
    } else if (s[0] == '-') {
      if (s[1] == '>') {
        tokens.emplace_back(eProduction::ktRightArrow);
        s = s.substr(2);
      } else
        return FailResult{std::format(
            "Unexpected codepoint encountered in source:'{}'.", s.at(1))};
    } else if (s[0] == '(') {
      tokens.emplace_back(eProduction::ktLeftParen);
      s = s.substr(1);
    } else if (s[0] == ')') {
      tokens.emplace_back(eProduction::ktRightParen);
      s = s.substr(1);
    } else if (s[0] == '|') {
      tokens.emplace_back(eProduction::ktVerticalLine);
      s = s.substr(1);
    } else if (s[0] == '\0') {
      break;  // Good end of file
    } else
      return FailResult{std::format(
          "Unexpected codepoint encountered in source:'{}'.", s.at(0))};
  }
  return tokens;
}

ExLexResult LexIdentifier(string_view s) noexcept {
  auto c = s.cbegin();
  while (c != s.cend() && std::isalnum(*c) || *c == '_' || *c == '$') c++;
  return LexResult{.tk = {eProduction::ktIdentifier, {s.begin(), c}},
                   .head = {c, s.end()}};
}

ExLexResult LexWhitespace(string_view s) noexcept {
  auto c = s.cbegin();
  while (c != s.cend() && *c == ' ' || *c == '\t') c++;
  return LexResult{.tk = {eProduction::ktNewline}, .head = {c, s.end()}};
}

ExLexResult LexNewline(string_view s) noexcept {
  auto c = s.cbegin();
  while (c != s.cend() && *c == '\n' || *c == '\r') c++;
  return LexResult{.tk = {eProduction::ktNewline}, .head = {c, s.cend()}};
}

ExLexResult LexEscapedCharSequence(string_view s) noexcept {
  auto c = s.cbegin();
  c++;
  while (!(c != s.end() && *c == '"' && *std::next(c, -1) != '\\')) {
    c++;
    if (*c == '"' && *std::next(c, -1) == '\\' && *std::next(c, -2) == '\\') {
      break;
    }
  }
  if (*c == '"') c++;
  return LexResult{.tk = {eProduction::ktStringLiteral, {s.begin(), c}},
                   .head = {c, s.end()}};
};

// <syntax> ::= <rule_decl>*
ExAst Parse(span<Tk> in) noexcept {
  using enum eProduction;
  auto it = in.cbegin();
  Ast syntax = {kiSyntax};
  while (it != in.cend()) {
    if (it->type == ktIdentifier) {
      auto next_rule = ParseRuleDecl(it, in.cend());
      if (!next_rule) return FailResult{next_rule.error()};
      syntax.branches.push_back(next_rule->ast);  // Append rules.
      it = next_rule->head;
      SkipIgnored(it, in.cend());
    } else
      return FailResult{
          "Expected rule identifier at start of rule declaration."};
  }
  return syntax;
}

// <ignored> ::= <WHITESPACE>*
// <ignored> ::= <NEWLINE>*
void SkipIgnored(TkSpanIter& it, const TkSpanIter& end) noexcept {
  while (it != end && it->type == eProduction::ktWhitespace ||
         it->type == eProduction::ktNewline)
    it++;
}

// <nonterminal> ::= <KW_E> | <IDENTIFIER>
// <terminal> ::= <STRING_LITERAL> | <CHAR_LITERAL>
ExParseResult ParseOperand(TkSpanIter it, TkSpanIter end) noexcept {
  using enum eProduction;
  if (it->type == ktIdentifier || it->type == ktStringLiteral) {
    return ParseResult{.ast = {it->type, string{it->literal}}, .head = it + 1};
  } else
    return FailResult{"Invalid operand."};
}

// <op_set> ::= ( <terminal> <opt_blank> ) *
// <op_set> ::= ( <nonterminal> <opt_blank> )*
ExParseResult ParseOperandSet(TkSpanIter it, TkSpanIter end) noexcept {
  using enum eProduction;
  // Opset may be a sub-set
  if (it->type == ktLeftParen) return ParseSubAlternative(it, end);

  // Expect atleast one operand.
  auto first_op = ParseOperand(it, end);
  if (!first_op) return first_op;
  Ast opset = {eProduction::kiOpSet};
  opset.branches.push_back(first_op->ast);
  it = first_op->head;
  SkipIgnored(it, end);

  while (true) {  // accumulate whitespace separated operands
    auto nextop = ParseOperand(it, end);
    if (!nextop) break;
    opset.branches.push_back(nextop->ast);
    it = nextop->head;
    SkipIgnored(it, end);
  }

  return ParseResult{opset, it};
}

// <alternative> ::= <op_set> <ignored> (<VERTICAL_LINE> <ignored> <alt>)*
// <alternative> ::= <op_set>
ExParseResult ParseAlternative(TkSpanIter it, TkSpanIter end) noexcept {
  using enum eProduction;
  if (it->type == ktLeftParen) return ParseSubAlternative(it, end);

  auto first_set = ParseOperandSet(it, end);
  if (!first_set)
    return FailResult("Expected atleast one operand set per alternative.");
  Ast alt = {kiAlternative};
  alt.branches.push_back(first_set->ast);
  it = first_set->head;
  SkipIgnored(it, end);

  while (true) {
    if (it->type == ktVerticalLine) {
      it++;
      SkipIgnored(it, end);

      auto next_set = ParseOperandSet(it, end);
      if (!next_set) return next_set;
      alt.branches.push_back(next_set->ast);
      it = next_set->head;
    } else
      break;
  }

  return ParseResult{alt, it};
}

// <alternative> ::= <LPAREN> <ignored> <alt> <ignored> <RPAREN>
ExParseResult ParseSubAlternative(TkSpanIter it, TkSpanIter end) noexcept {
  using enum eProduction;
  if (it->type == ktLeftParen)
    it++;  // skip initial paren.
  else
    return FailResult{"Sub alternative expected parentheses at the begining."};

  if (it->type == ktLeftParen) return ParseSubAlternative(it, end);
  SkipIgnored(it, end);

  auto first_set = ParseOperandSet(it, end);
  if (!first_set)
    return FailResult("Expected atleast one operand set per alternative.");
  Ast alt = {kiAlternative};
  alt.branches.push_back(first_set->ast);
  it = first_set->head;
  SkipIgnored(it, end);

  while (true) {
    if (it->type == ktVerticalLine) {
      it++;
      SkipIgnored(it, end);

      auto next_set = ParseOperandSet(it, end);
      if (!next_set) return next_set;
      alt.branches.push_back(next_set->ast);
      it = next_set->head;
    } else
      break;
  }

  SkipIgnored(it, end);
  // Expect a right paren to close the subexpr
  if (it->type != ktRightParen)
    return FailResult("Mismatched parentheses");
  else
    it++;

  return ParseResult{alt, it};
}

// <rule_decl> ::= <nonterminal> <ignored> <RIGHT_ARROW> <ignored> <alt>
//                 <ignored> <FULL_STOP> <ignored>
ExParseResult ParseRuleDecl(TkSpanIter it, TkSpanIter end) noexcept {
  using enum eProduction;
  if (it->type != ktIdentifier)
    return FailResult{"Expected rule identifier at start of rule declaration."};

  Ast decl = {kiRuleDecl};
  decl.branches.emplace_back(it->type, string{it->literal});  // Append id.
  it++;
  SkipIgnored(it, end);

  if (it->type != ktRightArrow)
    return FailResult{"Expected right arrow after rule name."};
  it++;
  SkipIgnored(it, end);

  auto rule_set = ParseAlternative(it, end);
  if (!rule_set) return rule_set;
  decl.branches.push_back(rule_set->ast);  // Append rules.
  it = rule_set->head;
  SkipIgnored(it, end);

  if (it->type != ktFullStop)
    return FailResult{"Expected a '.'(FullStop) at end of rule declaration."};
  it++;

  return ParseResult{decl, it};
}

}  // namespace cfg

std::expected<std::vector<char>, std::string> LoadFile(
    const std::filesystem::path& fp) {
  if (!std::filesystem::exists(fp))
    return std::unexpected<std::string>("Does not exist");

  if (!std::filesystem::is_regular_file(fp))
    return std::unexpected<std::string>("Not a regular file.");

  std::ifstream source_file_stream(fp);
  if (!source_file_stream.is_open())
    return std::unexpected<std::string>("Could not open file.");

  auto temp_file_buffer =
      std::vector<char>((std::istreambuf_iterator<char>(source_file_stream)),
                        std::istreambuf_iterator<char>());
  source_file_stream.close();

  // Add \0 if not already at end.
  if (temp_file_buffer.back() != '\0') temp_file_buffer.push_back('\0');

  return temp_file_buffer;
}

int main(int argc, char* argv[]) {
  using std::cout;
  using std::endl;
  using std::expected;
  using std::format;
  using std::print;
  using std::string;
  using std::string_view;
  using std::vector;

  vector<string> args{argv, argv + argc};
  if (args.size() < 2)
    cout << "[prs-cfg][error][cli] No CFG file path argument provided. Use "
            "command : prs-cfg \"filepath.ext\""
         << endl;

  expected<vector<char>, string> src = LoadFile(args[1]);
  if (!src)
    cout << format(
                "[prs-cfg][error][cli[ Could not load specified file "
                "path because:{}. Error path: {}",
                src.error(), args[1])
         << endl;
  string_view src_view = {src->begin(), src->end()};

  cfg::ExTk tokens = cfg::Lex(src_view);
  if (!tokens) {
    cout << "[prs-cfg][error] Failed to lex source file: "
         << tokens.error_or("Unknown Error") << endl;
    return 1;
  }

  cfg::ExAst ast = cfg::Parse(*tokens);
  if (!ast) {
    cout << "[prs-cfg][error][parser]: " + ast.error_or("Unknown Error")
         << endl;
    return 1;
  }

  if (ast) cout << FormatAst(*ast) << endl;

  cfg::IR ir{};
  for (const auto& rule_decl : ast->branches) ir.AddProduction(rule_decl);
  cout << ir.Format() << "\n\n" << endl;

  ir.ChomskyNormalFormStart();
  cout << ir.Format() << endl;
  ir.ChomskyNormalFormTerm();
  cout << ir.Format() << endl;
  ir.ChomskyNormalFormBIN();
  cout << ir.Format() << endl;
  ir.ApplyCnfUnitTransform();
  cout << ir.Format() << endl;
  return 0;
}
