include "../lib/Seq.dfy"
include "../lib/seq/Count.dfy"

import opened Seq
import opened SeqCount

// function Count<T>(xs: seq<T>, v: T): int {
//   Foldl'((r, x)=> r + (if x == v then 1 else 0), 0, xs)
// }

method RemoveElement(nums: array<int>, val: int) returns (length: nat)
  modifies nums
  ensures length <= nums.Length
  ensures length == nums.Length - Count(old(nums[..]), val)
  ensures forall k :: 0 <= k < length ==> nums[k] != val
  ensures forall x :: x != val && x in old(nums[..]) ==> x in nums[..length]
  ensures forall x :: x != val ==> Count(nums[..length], x) == Count(old(nums[..]), x)
{
  var j, i := 0, 0;
  while i < nums.Length
    invariant 0 <= j <= i <= nums.Length
    invariant forall k :: 0 <= k < j ==> nums[k] != val
    invariant j == i - Count(old(nums[..i]), val)
    invariant old(nums[i..]) == nums[i..]
    invariant forall k :: 0 <= k < i ==> (old(nums[k]) != val <==> old(nums[k]) in nums[..j])
    invariant forall m :: 0 <= m < j ==> exists k :: 0 <= k < i && old(nums[k]) == nums[m]
    invariant forall k :: 0 <= k < i && old(nums[k]) != val ==> Count(nums[..j], old(nums[k])) == Count(old(nums[..i]), old(nums[k]))
  {
    assert nums[i] == old(nums[i]);
    assert old(nums[..i + 1]) == old(nums[..i]) + [old(nums[i])];
    CountConcat(old(nums[..i]), [old(nums[i])], val);
    if nums[i] != val {
      nums[j] := nums[i];
      assert nums[..j + 1] == nums[..j] + [nums[i]];
      CountConcat(nums[..j], [nums[i]], nums[i]);
      assert Count(nums[..j + 1], nums[i]) == 1 + Count(nums[..j], nums[i]);
      CountConcat(old(nums[..i]), [old(nums[i])], nums[i]);
      assert Count(old(nums[..i + 1]), nums[i]) == 1 + Count(old(nums[..i]), nums[i]);

      assert Count(nums[..j + 1], nums[i]) == Count(old(nums[..i + 1]), nums[i]) by {
        if exists k :: 0 <= k < i && old(nums[k]) == nums[i] {
          ghost var k :| 0 <= k < i && old(nums[k]) == nums[i];
          assert old(nums[k]) != val;
          assert Count(nums[..j], old(nums[k])) == Count(old(nums[..i]), old(nums[k]));
        } else {
          assert nums[i] !in nums[..j] by {
            if nums[i] in nums[..j] {
              var m :| 0 <= m < j && nums[m] == nums[i];
              var k :| 0 <= k < i && old(nums[k]) == nums[m];
              assert old(nums[k]) == nums[i];
              assert false;
            }
          }
          Count0(nums[..j], nums[i]);
          assert nums[i] !in old(nums[..i]) by {
            if nums[i] in old(nums[..i]) {
              var k :| 0 <= k < i && old(nums[..i])[k] == nums[i];
              assert old(nums[k]) == nums[i];
              assert false;
            }
          }
          Count0(old(nums[..i]), nums[i]);
        }
      }
      // Maintain per-element Count invariant for k < i (k == i handled above)
      forall k | 0 <= k < i && old(nums[k]) != val
        ensures Count(nums[..j + 1], old(nums[k])) == Count(old(nums[..i + 1]), old(nums[k]))
      {
        CountConcat(nums[..j], [nums[i]], old(nums[k]));
        CountConcat(old(nums[..i]), [old(nums[i])], old(nums[k]));
      }
      // Maintain "every element of nums[..j+1] came from old"
      forall m | 0 <= m < j + 1
        ensures exists k :: 0 <= k < i + 1 && old(nums[k]) == nums[m]
      {
        if m < j {
          var k :| 0 <= k < i && old(nums[k]) == nums[m];
        } else {
          assert nums[m] == old(nums[i]);
        }
      }
      j := j + 1;
    } else {
      // nums[i] == val; nums and j unchanged
      forall k | 0 <= k < i && old(nums[k]) != val
        ensures Count(nums[..j], old(nums[k])) == Count(old(nums[..i + 1]), old(nums[k]))
      {
        CountConcat(old(nums[..i]), [old(nums[i])], old(nums[k]));
      }
    }
    assert old(nums[i + 1..]) == nums[i + 1..];
    assert old(nums[..i + 1]) == old(nums[..i]) + old([nums[i]]);
    i := i + 1;
  }
  assert old(nums[..i]) == old(nums[..]);
  forall x | x != val
    ensures Count(nums[..j], x) == Count(old(nums[..]), x)
  {
    if x in old(nums[..]) {
      var k :| 0 <= k < nums.Length && old(nums[..])[k] == x;
      assert old(nums[k]) == x;
      assert old(nums[k]) != val;
      assert Count(nums[..j], old(nums[k])) == Count(old(nums[..i]), old(nums[k]));
    } else {
      Count0(old(nums[..]), x);
      assert x !in nums[..j] by {
        if x in nums[..j] {
          var m :| 0 <= m < j && nums[m] == x;
          var k :| 0 <= k < nums.Length && old(nums[k]) == nums[m];
          assert old(nums[k]) == x;
          assert x in old(nums[..]);
          assert false;
        }
      }
      Count0(nums[..j], x);
    }
  }
  return j;
}

// method RemoveElement2(nums: array<int>, val: int) returns (length: nat)
//   modifies nums
//   ensures length <= nums.Length
//   ensures forall k :: 0 <= k < length ==> nums[k] != val
//   // ensures forall x :: x != val && x in old(nums[..]) ==> x in nums[..length]
// {
//   var j, i := nums.Length, 0;
//   while i < j
//     invariant 0 <= i <= j <= nums.Length
//     invariant forall k :: 0 <= k < i ==> nums[k] != val
//     invariant old(nums[j..]) == nums[j..]
//     // invariant forall k :: 0 <= k < i && old(nums[k]) != val ==> old(nums[k]) in nums[..i]
//   {
//     if nums[i] == val {
//       assert old(nums[j..]) == nums[j..];
//       assert nums[j - 1..] == [nums[j - 1]] + nums[j..];
//       if j == i + 1 {
//         assume false;
//       } else {
//         assume false;
//       }
//       j := j - 1;
//       nums[i] := nums[j];
//     } else {
//       // assert nums[..i + 1] == nums[..i] + [nums[i]];
//       // assert old(nums[i]) == nums[i];
//       i := i + 1;
//     }
//   }
//   return j;
// }