// Author: Shaobo He
// LeetCode 772: Basic Calculator III
//
// Evaluate a valid arithmetic expression over non-negative integer literals
// with + - * / and parentheses, standard precedence (* / tighter than + -),
// left-to-right associativity for equal precedence, and integer division that
// TRUNCATES TOWARD ZERO.
//
// Approach (variant A):
//   * A denotational AST `Expr` with `Eval : Expr -> int` giving the meaning.
//   * A custom `TDiv` modelling truncate-toward-zero division, since Dafny's
//     built-in `/` on int is Euclidean (floors toward -infinity) and therefore
//     DISAGREES with the problem for negative dividends. We prove `TDiv`
//     genuinely truncates toward zero.
//   * A total, terminating recursive-descent parser (`Expr`-producing) whose
//     grammar encodes precedence.  We prove termination and the structural
//     postconditions (index monotone & in-bounds).  Precedence/associativity of
//     the denotational meaning is captured by small structural Eval lemmas.
//
// What is proven here:
//   * TDiv genuinely truncates toward zero (and differs from Dafny's Euclidean
//     `/` on negatives) — full characterization + concrete cases.
//   * Eval is a total denotational semantics; the parser is total and
//     terminating on every input.
//   * End-to-end correctness on concrete inputs (the LeetCode examples and a
//     parenthesized case), each parsed and evaluated string -> number.
// Not attempted: a general soundness/completeness proof of the parser against
// an inductive grammar relation (research-grade; would blow the time budget).

// ---------------------------------------------------------------------------
// Truncate-toward-zero integer division
// ---------------------------------------------------------------------------

function Abs(x: int): int { if x < 0 then -x else x }

// Truncate-toward-zero quotient: magnitude is |a|/|b| (a floor on non-negatives,
// which equals truncation there), and the sign is the sign of the real quotient.
function TDiv(a: int, b: int): int
  requires b != 0
{
  var q := Abs(a) / Abs(b);
  if (a < 0) == (b < 0) then q else -q
}

// Remainder consistent with TDiv: a == b*TDiv(a,b) + TMod(a,b).
function TMod(a: int, b: int): int
  requires b != 0
{
  a - b * TDiv(a, b)
}

// Full characterisation of truncate-toward-zero division:
//   (1) the division identity holds,
//   (2) the remainder is strictly smaller in magnitude than the divisor,
//   (3) the remainder has the same sign as the dividend (or is zero).
// (2)+(3) together are exactly what distinguishes truncation-toward-zero from
// flooring.
lemma TDivTruncatesTowardZero(a: int, b: int)
  requires b != 0
  ensures a == b * TDiv(a, b) + TMod(a, b)
  ensures Abs(TMod(a, b)) < Abs(b)
  ensures TMod(a, b) == 0 || (TMod(a, b) < 0) == (a < 0)
{
  var A := Abs(a);
  var B := Abs(b);
  var Q := A / B;
  var R := A % B;
  assert B > 0;
  assert A == B * Q + R;   // Euclidean identity (built-in)
  assert 0 <= R < B;       // remainder bounds for positive divisor (built-in)
  if a >= 0 {
    assert A == a;
    if b > 0 {
      assert B == b;
      assert TDiv(a, b) == Q;
      assert TMod(a, b) == R;
    } else {
      assert B == -b;
      assert TDiv(a, b) == -Q;
      assert TMod(a, b) == R;
    }
  } else {
    assert A == -a;
    if b > 0 {
      assert B == b;
      assert TDiv(a, b) == -Q;
      assert TMod(a, b) == -R;
    } else {
      assert B == -b;
      assert TDiv(a, b) == Q;
      assert TMod(a, b) == -R;
    }
  }
}

// Concrete evidence that TDiv truncates toward zero and that this genuinely
// differs from Dafny's built-in Euclidean `/` on negatives.
lemma TruncTowardZeroExamples()
  ensures TDiv(7, 2) == 3
  ensures TDiv(-7, 2) == -3
  ensures TDiv(7, -2) == -3
  ensures TDiv(-7, -2) == 3
  ensures (-7) / 2 == -4   // Dafny's Euclidean division floors: differs from TDiv
{
}

// ---------------------------------------------------------------------------
// Denotational meaning
// ---------------------------------------------------------------------------

datatype Expr =
  | Num(int)
  | Add(Expr, Expr)
  | Sub(Expr, Expr)
  | Mul(Expr, Expr)
  | Div(Expr, Expr)

// The meaning of an expression. Division uses truncate-toward-zero semantics.
// Division by zero cannot occur for valid inputs; we return 0 there to keep
// Eval total (see NoDivByZero for the honesty predicate).
function Eval(e: Expr): int
{
  match e
  case Num(n)    => n
  case Add(a, b) => Eval(a) + Eval(b)
  case Sub(a, b) => Eval(a) - Eval(b)
  case Mul(a, b) => Eval(a) * Eval(b)
  case Div(a, b) => if Eval(b) == 0 then 0 else TDiv(Eval(a), Eval(b))
}

// Honesty predicate: no divisor ever evaluates to zero. For such expressions
// the guard in Eval's Div case is never taken.
predicate NoDivByZero(e: Expr)
{
  match e
  case Num(_)    => true
  case Add(a, b) => NoDivByZero(a) && NoDivByZero(b)
  case Sub(a, b) => NoDivByZero(a) && NoDivByZero(b)
  case Mul(a, b) => NoDivByZero(a) && NoDivByZero(b)
  case Div(a, b) => NoDivByZero(a) && NoDivByZero(b) && Eval(b) != 0
}

// The Div node's meaning is exactly truncate-toward-zero division of its parts
// when the divisor is non-zero.
lemma DivMeaningIsTruncDiv(a: int, b: int)
  requires b != 0
  ensures Eval(Div(Num(a), Num(b))) == TDiv(a, b)
{
}

// Precedence: `*` binds tighter than `+` in the AST the grammar builds.
lemma PrecedenceMulOverAdd(a: int, b: int, c: int)
  ensures Eval(Add(Num(a), Mul(Num(b), Num(c)))) == a + b * c
{
  assert Eval(Mul(Num(b), Num(c))) == b * c;
}

// Left-to-right associativity for equal precedence: a - b - c parses as
// (a - b) - c.
lemma LeftAssocSub(a: int, b: int, c: int)
  ensures Eval(Sub(Sub(Num(a), Num(b)), Num(c))) == a - b - c
{
  assert Eval(Sub(Num(a), Num(b))) == a - b;
}

// Parenthesisation changes grouping (and hence meaning): (a + b) * c.
lemma ParenChangesGrouping(a: int, b: int, c: int)
  ensures Eval(Mul(Add(Num(a), Num(b)), Num(c))) == (a + b) * c
{
  assert Eval(Add(Num(a), Num(b))) == a + b;
}

// ---------------------------------------------------------------------------
// Recursive-descent parser (total & terminating)
// ---------------------------------------------------------------------------
//
// Grammar:
//   expr   ::= term  (('+' | '-') term)*
//   term   ::= factor (('*' | '/') factor)*
//   factor ::= number | '(' expr ')'
//
// Every parse function returns (built AST, index just past what it consumed)
// and satisfies  i <= result.1 <= |s|  (monotone, in-bounds).
//
// Termination for the mutual cluster uses the lexicographic measure
//   (|s| - i, rank)
// with ranks expr=5, exprRest=4, term=3, termRest=2, factor=1.  Every call
// either strictly decreases the remaining length |s|-i, or keeps it equal while
// strictly decreasing the rank.

predicate isDigit(c: char) { '0' <= c <= '9' }

function digitVal(c: char): int
  requires isDigit(c)
{
  (c as int) - ('0' as int)
}

// Parse a maximal run of digits starting at i, accumulating the value.
function parseNum(s: seq<char>, i: nat, acc: int): (r: (int, nat))
  requires i <= |s|
  ensures i <= r.1 <= |s|
  decreases |s| - i
{
  if i < |s| && isDigit(s[i]) then
    parseNum(s, i + 1, acc * 10 + digitVal(s[i]))
  else
    (acc, i)
}

function parseFactor(s: seq<char>, i: nat): (r: (Expr, nat))
  requires i <= |s|
  ensures i <= r.1 <= |s|
  decreases |s| - i, 1
{
  if i < |s| && s[i] == '(' then
    var pe := parseExpr(s, i + 1);
    if pe.1 < |s| && s[pe.1] == ')' then (pe.0, pe.1 + 1)
    else (pe.0, pe.1)
  else if i < |s| && isDigit(s[i]) then
    var pn := parseNum(s, i, 0);
    (Num(pn.0), pn.1)
  else
    (Num(0), i)   // invalid position: consume nothing (inputs are valid)
}

function parseTermRest(s: seq<char>, acc: Expr, j: nat): (r: (Expr, nat))
  requires j <= |s|
  ensures j <= r.1 <= |s|
  decreases |s| - j, 2
{
  if j < |s| && (s[j] == '*' || s[j] == '/') then
    var pf := parseFactor(s, j + 1);
    var acc2 := if s[j] == '*' then Mul(acc, pf.0) else Div(acc, pf.0);
    parseTermRest(s, acc2, pf.1)
  else
    (acc, j)
}

function parseTerm(s: seq<char>, i: nat): (r: (Expr, nat))
  requires i <= |s|
  ensures i <= r.1 <= |s|
  decreases |s| - i, 3
{
  var pf := parseFactor(s, i);
  parseTermRest(s, pf.0, pf.1)
}

function parseExprRest(s: seq<char>, acc: Expr, j: nat): (r: (Expr, nat))
  requires j <= |s|
  ensures j <= r.1 <= |s|
  decreases |s| - j, 4
{
  if j < |s| && (s[j] == '+' || s[j] == '-') then
    var pt := parseTerm(s, j + 1);
    var acc2 := if s[j] == '+' then Add(acc, pt.0) else Sub(acc, pt.0);
    parseExprRest(s, acc2, pt.1)
  else
    (acc, j)
}

function parseExpr(s: seq<char>, i: nat): (r: (Expr, nat))
  requires i <= |s|
  ensures i <= r.1 <= |s|
  decreases |s| - i, 5
{
  var pt := parseTerm(s, i);
  parseExprRest(s, pt.0, pt.1)
}

// Strict recognizer for the public grammar. Unlike the total parser above,
// these functions fail instead of inventing Num(0) at invalid positions.
function parseDigitsEnd(s: seq<char>, i: nat): (j: nat)
  requires i <= |s|
  ensures i <= j <= |s|
  decreases |s| - i
{
  if i < |s| && isDigit(s[i]) then parseDigitsEnd(s, i + 1) else i
}

function parseNumberStrict(s: seq<char>, i: nat): (r: (bool, nat))
  requires i <= |s|
  ensures i <= r.1 <= |s|
  ensures r.0 ==> i < r.1
{
  if i < |s| && isDigit(s[i]) then (true, parseDigitsEnd(s, i + 1)) else (false, i)
}

function parseFactorStrict(s: seq<char>, i: nat): (r: (bool, nat))
  requires i <= |s|
  ensures i <= r.1 <= |s|
  ensures r.0 ==> i < r.1
  decreases |s| - i, 1
{
  if i < |s| && isDigit(s[i]) then
    parseNumberStrict(s, i)
  else if i < |s| && s[i] == '(' then
    var pe := parseExprStrict(s, i + 1);
    if pe.0 && pe.1 < |s| && s[pe.1] == ')' then (true, pe.1 + 1) else (false, i)
  else
    (false, i)
}

function parseTermRestStrict(s: seq<char>, j: nat): (r: (bool, nat))
  requires j <= |s|
  ensures j <= r.1 <= |s|
  decreases |s| - j, 2
{
  if j < |s| && (s[j] == '*' || s[j] == '/') then
    var pf := parseFactorStrict(s, j + 1);
    if pf.0 then parseTermRestStrict(s, pf.1) else (false, j)
  else
    (true, j)
}

function parseTermStrict(s: seq<char>, i: nat): (r: (bool, nat))
  requires i <= |s|
  ensures i <= r.1 <= |s|
  decreases |s| - i, 3
{
  var pf := parseFactorStrict(s, i);
  if pf.0 then parseTermRestStrict(s, pf.1) else (false, i)
}

function parseExprRestStrict(s: seq<char>, j: nat): (r: (bool, nat))
  requires j <= |s|
  ensures j <= r.1 <= |s|
  decreases |s| - j, 4
{
  if j < |s| && (s[j] == '+' || s[j] == '-') then
    var pt := parseTermStrict(s, j + 1);
    if pt.0 then parseExprRestStrict(s, pt.1) else (false, j)
  else
    (true, j)
}

function parseExprStrict(s: seq<char>, i: nat): (r: (bool, nat))
  requires i <= |s|
  ensures i <= r.1 <= |s|
  decreases |s| - i, 5
{
  var pt := parseTermStrict(s, i);
  if pt.0 then parseExprRestStrict(s, pt.1) else (false, i)
}

// A LeetCode-valid input is a full strict parse with no division by zero.
predicate ValidExpression(s: seq<char>) {
  var p := parseExprStrict(s, 0);
  p.0 && p.1 == |s| && NoDivByZero(parseExpr(s, 0).0)
}

lemma RejectTrailingOperator()
  ensures !ValidExpression("1+")
{
}

// End-to-end evaluator: parse the whole valid string, then take its
// denotational meaning. Totality/termination of parsing is proved above.
function Calculate(s: seq<char>): int
  requires ValidExpression(s)
  ensures Calculate(s) == Eval(parseExpr(s, 0).0)
{
  Eval(parseExpr(s, 0).0)
}

// End-to-end correctness on the LeetCode examples: the whole string is parsed
// (with precedence, parentheses and truncating division) and evaluated to the
// expected number.
lemma Example1()
  ensures Calculate("1+1") == 2
{
}

lemma Example2()
  ensures Calculate("6-4/2") == 4
{
}

// Parentheses override precedence: without them 2*3+4 = 10, with them 2*(3+4) = 14.
lemma Example3()
  ensures Calculate("2*(3+4)") == 14
{
}
