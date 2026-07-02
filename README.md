# dafny_examples

A collection of Dafny proofs: verified solutions to LeetCode problems plus a
small reusable library of lemmas and data-structure helpers.

[![check proofs](https://github.com/shaobo-he/dafny_examples/actions/workflows/ci.yaml/badge.svg)](https://github.com/shaobo-he/dafny_examples/actions/workflows/ci.yaml)

## Layout

- `leetcode/` — 26 LeetCode problems with verified specs (sqrt, two-sum, max
  subarray, k-th factor, invert/symmetric binary tree, range update, merge
  sorted array, merge k sorted lists, best-time-to-buy-and-sell-stock, LRU
  cache, basic calculator III, burst balloons, trapping rain water II, etc.).
- `lib/`
  - `Seq.dfy`, `SeqMethods.dfy`, `List.dfy`, `MinMax.dfy`, `Pow.dfy` —
    sequence and arithmetic utilities.
  - `seq/` — `Count`, `Digits`, `Fold`, `Map`, `Palindrome`, `Subseq`, `Undup`.
  - `math/` — `Abs`, `DivMod`, `EvenOdd`, `Factors`, `Gcd`.
  - `adt/` — `BinaryTree`, `BST`, `Graph` (topological sort via Kahn's BFS),
    `PriorityQueue` (min leftist heap).
- Root-level `.dfy` files — small standalone experiments (vector class, set
  abstractions, shuffle/random-entry methods).

## Toolchain

- **Dafny 4.11.0** (bundles Z3 4.12.1 / 4.14.1).
- Download the official release zip from
  [the Dafny releases page](https://github.com/dafny-lang/dafny/releases/tag/v4.11.0)
  — installing via `dotnet tool install Dafny` does **not** ship a Z3 binary,
  so verification will fail.

## Verify locally

Single file:

```sh
dafny verify lib/Seq.dfy
```

Everything (skipping any `[wip]`-prefixed files, in parallel):

```sh
find . -name '*.dfy' | awk '!/\[wip\]/' \
  | xargs -I{} -P 8 -n 1 timeout 120 dafny verify {}
```

## CI

`.github/workflows/ci.yaml` runs `dafny verify` on every `.dfy` file across
six matrix slices (one per directory). `[wip]`-prefixed files are skipped.

## License

See [LICENSE](LICENSE).
