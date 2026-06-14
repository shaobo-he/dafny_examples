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

method Generate(n: nat) returns (result: seq<string>)
  ensures forall s :: s in result ==> |s| == 2 * n && WellFormed(s)
{
  result := Gen(n, n, "");
}

method Gen(open: nat, close: nat, prefix: string) returns (result: seq<string>)
  requires open <= close
  requires OnlyParens(prefix)
  requires Balanced(prefix)
  requires Count(prefix, '(') + open == Count(prefix, ')') + close
  ensures forall s :: s in result ==> |s| == |prefix| + open + close && WellFormed(s)
  decreases open + close
{
  if open == 0 && close == 0 {
    return [prefix];
  }
  result := [];
  if open > 0 {
    BalancedAppend(prefix, '(');
    var prefix' := prefix + "(";
    CountConcat(prefix, "(", '(');
    CountConcat(prefix, "(", ')');
    assert OnlyParens(prefix');
    var r1 := Gen(open - 1, close, prefix');
    result := result + r1;
  }
  if close > open {
    BalancedAppend(prefix, ')');
    var prefix' := prefix + ")";
    CountConcat(prefix, ")", '(');
    CountConcat(prefix, ")", ')');
    assert OnlyParens(prefix');
    var r2 := Gen(open, close - 1, prefix');
    result := result + r2;
  }
}
