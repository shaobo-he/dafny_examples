// LeetCode 1: Two Sum.
// Note on the "minimality" postcondition (forall i<j<r.1 :: sum != target): it
// pins r.1 as the SMALLEST possible second index of any solution; among pairs
// ending at r.1 it returns one valid first index (the map keeps the latest
// equal-valued complement seen), but r.0 is not claimed to be the globally smallest first
// index. This is the "earliest solution by second index" notion, not the
// lexicographically-smallest pair.
//
// If this invariant is added explicitly to the loop then the verfication never finishes.
// It could be {:opaque} for a more controlled verification:
// assert InMap([], m, target) by {
//   reveal InMap();
// }
predicate InMap(nums: seq<int>, m: map<int, int>, t: int) {
  forall j :: 0 <= j < |nums| ==> t - nums[j] in m
}

method TwoSum(nums: array<int>, target: int) returns (r: (int, int))
  ensures r.0 == -1 || 0 <= r.0
  ensures 0 <= r.0 ==> 0 <= r.0 < r.1 < nums.Length &&
                       nums[r.0] + nums[r.1] == target &&
                       forall i, j :: 0 <= i < j < r.1 ==> nums[i] + nums[j] != target
  ensures (exists i, j :: 0 <= i < j < nums.Length && nums[i] + nums[j] == target) ==>
            0 <= r.0 < r.1 < nums.Length && nums[r.0] + nums[r.1] == target
  ensures r.0 == -1 ==> r.1 == -1
  ensures r.0 == -1 <==> forall i, j :: 0 <= i < j < nums.Length ==> nums[i] + nums[j] != target
{
  var m: map<int, int> := map[];
  var i := 0;
  while i < nums.Length
    invariant i <= nums.Length
    invariant forall k :: k in m ==> 0 <= m[k] < i
    invariant forall k :: k in m ==> nums[m[k]] + k == target
    invariant InMap(nums[..i], m, target)
    invariant forall u, v :: 0 <= u < v < i ==> nums[u] + nums[v] != target
  {
    if nums[i] in m {
      return (m[nums[i]], i);
    }
    m := m[target - nums[i] := i];
    i := i + 1;
  }
  return (-1, -1);
}

method {:test} TestTwoSum()
{
  var nums := new int[4];
  nums[0], nums[1], nums[2], nums[3] := 2, 7, 11, 15;
  var r := TwoSum(nums, 9);
  expect r == (0, 1), "[2,7,11,15], target 9 should return (0,1)";

  var none := new int[3];
  none[0], none[1], none[2] := 1, 2, 4;
  var missing := TwoSum(none, 8);
  expect missing == (-1, -1), "no-solution case should return (-1,-1)";
}
