// Author: Shaobo He
// LeetCode 22: Generate Parentheses
// Given n pairs of parentheses, generate all combinations of well-formed parentheses.

include "../lib/seq/Count.dfy"

import opened SeqCount

predicate OnlyParens(s: string) {
  forall i :: 0 <= i < |s| ==> s[i] == '(' || s[i] == ')'
}

predicate Balanced(s: string) {
  forall i :: 0 <= i <= |s| ==> Count(s[..i], '(') >= Count(s[..i], ')')
}

predicate WellFormed(s: string) {
  OnlyParens(s) && Balanced(s) && Count(s, '(') == Count(s, ')')
}

predicate Distinct<T(==)>(xs: seq<T>) {
  forall i, j :: 0 <= i < j < |xs| ==> xs[i] != xs[j]
}

lemma DistinctConcatDisjoint<T>(xs: seq<T>, ys: seq<T>)
  requires Distinct(xs) && Distinct(ys)
  requires forall x :: x in xs ==> x !in ys
  ensures Distinct(xs + ys)
{
  forall i, j | 0 <= i < j < |xs + ys|
    ensures (xs + ys)[i] != (xs + ys)[j]
  {
    if i < |xs| && j < |xs| {
    } else if i < |xs| {
      assert (xs + ys)[i] in xs;
      assert (xs + ys)[j] in ys;
    } else {
      assert (xs + ys)[i] == ys[i - |xs|];
      assert (xs + ys)[j] == ys[j - |xs|];
    }
  }
}

lemma InConcat<T>(xs: seq<T>, ys: seq<T>, x: T)
  ensures x in xs + ys <==> x in xs || x in ys
{
}

lemma BalancedAppend(s: string, c: char)
  requires Balanced(s)
  requires c == '(' || (c == ')' && Count(s, '(') > Count(s, ')'))
  ensures Balanced(s + [c])
{
  var t := s + [c];
  forall i | 0 <= i <= |t|
    ensures Count(t[..i], '(') >= Count(t[..i], ')')
  {
    if i <= |s| {
      assert t[..i] == s[..i];
    } else {
      assert i == |s| + 1;
      assert t[..i] == s + [c];
      assert s[..|s|] == s;
      CountConcat(s, [c], '(');
      CountConcat(s, [c], ')');
    }
  }
}

lemma CountParensSum(s: string)
  requires OnlyParens(s)
  ensures Count(s, '(') + Count(s, ')') == |s|
{
  if |s| > 0 {
    assert OnlyParens(s[1..]);
    CountParensSum(s[1..]);
  }
}

lemma OnlyParensSuffix(s: string, k: int)
  requires 0 <= k <= |s| && OnlyParens(s)
  ensures OnlyParens(s[k..])
{
}

method Generate(n: nat) returns (result: seq<string>)
  // Soundness: every generated string is a well-formed length-2n parenthesization.
  ensures forall s :: s in result ==> |s| == 2 * n && WellFormed(s)
  ensures Distinct(result)
  // Completeness: every well-formed length-2n parenthesization is generated.
  ensures forall s :: |s| == 2 * n && WellFormed(s) ==> s in result
{
  result := Gen(n, n, "");
}

method Gen(open: nat, close: nat, prefix: string) returns (result: seq<string>)
  requires open <= close
  requires OnlyParens(prefix)
  requires Balanced(prefix)
  requires Count(prefix, '(') + open == Count(prefix, ')') + close
  ensures forall s :: s in result ==> |s| == |prefix| + open + close && WellFormed(s)
  ensures forall s :: s in result ==> s[..|prefix|] == prefix
  ensures Distinct(result)
  // Completeness: every well-formed string of the right length that extends
  // prefix is produced.
  ensures forall s :: (|s| == |prefix| + open + close && WellFormed(s) && s[..|prefix|] == prefix)
                      ==> s in result
  decreases open + close
{
  if open == 0 && close == 0 {
    result := [prefix];
    assert Distinct(result);
    forall s | |s| == |prefix| && WellFormed(s) && s[..|prefix|] == prefix
      ensures s in result
    {
      assert s == prefix;
    }
    return;
  }

  var r1: seq<string> := [];
  var r2: seq<string> := [];
  if open > 0 {
    BalancedAppend(prefix, '(');
    var p := prefix + "(";
    CountConcat(prefix, "(", '(');
    CountConcat(prefix, "(", ')');
    assert OnlyParens(p);
    r1 := Gen(open - 1, close, p);
  }
  if close > open {
    BalancedAppend(prefix, ')');
    var p := prefix + ")";
    CountConcat(prefix, ")", '(');
    CountConcat(prefix, ")", ')');
    assert OnlyParens(p);
    r2 := Gen(open, close - 1, p);
  }
  forall s | s in r1
    ensures s !in r2
  {
    assert open > 0;
    var p1 := prefix + "(";
    assert s[..|p1|] == p1;
    if s in r2 {
      assert close > open;
      var p2 := prefix + ")";
      assert s[..|p2|] == p2;
      assert p1[|prefix|] == '(';
      assert p2[|prefix|] == ')';
      assert false;
    }
  }
  DistinctConcatDisjoint(r1, r2);
  result := r1 + r2;

  forall s | s in result
    ensures s[..|prefix|] == prefix
  {
    InConcat(r1, r2, s);
    if s in r1 {
    } else {
      assert s in r2;
    }
  }

  forall s | |s| == |prefix| + open + close && WellFormed(s) && s[..|prefix|] == prefix
    ensures s in result
  {
    var suf := s[|prefix|..];
    assert s == prefix + suf;
    assert |prefix| < |s|;
    CountConcat(prefix, suf, '(');
    CountConcat(prefix, suf, ')');
    CountParensSum(s);
    OnlyParensSuffix(s, |prefix|);
    CountParensSum(suf);
    // suffix has exactly `open` '(' and `close` ')' (from WellFormed + precondition).
    assert Count(suf, '(') == open && Count(suf, ')') == close;

    if s[|prefix|] == '(' {
      assert suf[0] == '(';
      assert open >= 1;                                  // Count(suf,'(') >= 1
      assert s[..|prefix| + 1] == prefix + "(";
      // s extends prefix+"(" with (open-1, close), so it is in r1.
      assert s in r1;
    } else {
      assert s[|prefix|] == ')';
      assert s[..|prefix| + 1] == prefix + ")";
      CountConcat(prefix, ")", '(');
      CountConcat(prefix, ")", ')');
      assert Count(s[..|prefix| + 1], '(') >= Count(s[..|prefix| + 1], ')');  // Balanced(s)
      assert close > open;
      assert s in r2;
    }
  }
}
