# Tree Benchmark Results (RedBlackTree vs BTreeSet)

Benchmark conducted using Criterion.rs with 10,000 operations per test.

## Insert Operations (10,000 elements)

| Operation | RedBlackTree | BTreeSet | Winner |
|-----------|--------------|----------|---------|
| Sequential Insert | 707.81µs | 416.47µs | **BTreeSet 1.7x faster** |
| Random Insert | 1.24ms | 569.21µs | **BTreeSet 2.2x faster** |
| Reverse Insert | 1.00ms | 169.40µs | **BTreeSet 5.9x faster** |

## Lookup Operations (10,000 elements)

| Operation | RedBlackTree | BTreeSet | Winner |
|-----------|--------------|----------|---------|
| Sequential Lookup | 304.62µs | 312.77µs | **RedBlackTree 1.03x faster** |
| Random Lookup | 177.56µs | 220.17µs | **RedBlackTree 1.24x faster** |

## Other Operations

| Operation | RedBlackTree | BTreeSet | Winner |
|-----------|--------------|----------|---------|
| Mixed Operations | 673.84µs | 326.90µs | **BTreeSet 2.1x faster** |
| Clear | 56.15µs | 36.52µs | **BTreeSet 1.5x faster** |
| Duplicate Inserts | 13.86µs | 24.62µs | **RedBlackTree 1.8x faster** |

## Size Scaling Performance

| Elements | RedBlackTree | BTreeSet | BTreeSet Advantage |
|----------|--------------|----------|-------------------|
| 1,000 | 96.29µs | 28.83µs | **3.3x faster** |
| 5,000 | 757.19µs | 199.91µs | **3.8x faster** |
| 10,000 | 1.64ms | 428.17µs | **3.8x faster** |
| 25,000 | 3.63ms | 1.13ms | **3.2x faster** |

## Key Insights

### BTreeSet Advantages:
- **Dominates insertion operations** - Especially for sequential and reverse patterns
- **Better scaling characteristics** - Maintains 3-4x advantage across all sizes
- **Superior mixed operation performance** - 2x faster for realistic usage patterns
- **Faster clear operations** - More efficient memory deallocation

### RedBlackTree Advantages:
- **Slight lookup performance edge** - Particularly for random access patterns
- **Better duplicate handling** - Nearly 2x faster for duplicate insertions
- **More predictable worst-case** - Traditional red-black tree guarantees

### Performance Analysis:
1. **BTreeSet's cache-friendly B-tree structure** provides significant advantages for most operations
2. **RedBlackTree's `with_capacity` optimization** works well but can't overcome algorithmic differences
3. **Memory locality** appears to be the key differentiator favoring BTreeSet
4. **Random access patterns** slightly favor RedBlackTree's pointer-based structure

## Recommendation

For most use cases, **BTreeSet** is the better choice due to its superior insertion performance and scaling characteristics. Consider **RedBlackTree** only when:
- Random lookup performance is critical
- Duplicate insertion handling is a primary concern
- Specific red-black tree properties are required

## Benchmark Configuration

- **Tool**: Criterion.rs with statistical analysis
- **Operations**: 10,000 per test (except size scaling)
- **Optimization**: Both implementations use `with_capacity()` where available
- **Environment**: Release mode compilation
- **Measurements**: 100 samples per benchmark with outlier detection

## Raw Criterion Results

```
insert_sequential/RedBlackTree
                        time:   [697.82 µs 707.81 µs 716.52 µs]
                        change: [-2.7948% +0.0849% +3.0399%] (p = 0.96 > 0.05)
                        No change in performance detected.
Found 1 outliers among 100 measurements (1.00%)
  1 (1.00%) low mild

insert_sequential/BTreeSet
                        time:   [415.37 µs 416.47 µs 417.43 µs]
                        change: [-1.5278% -0.7058% -0.0221%] (p = 0.07 > 0.05)
                        No change in performance detected.
Found 1 outliers among 100 measurements (1.00%)
  1 (1.00%) high mild

insert_random/RedBlackTree
                        time:   [1.2352 ms 1.2439 ms 1.2519 ms]
                        change: [-7.3982% -1.9532% +3.6510%] (p = 0.53 > 0.05)
                        No change in performance detected.
Found 11 outliers among 100 measurements (11.00%)
  6 (6.00%) low severe
  1 (1.00%) low mild
  1 (1.00%) high mild
  3 (3.00%) high severe

insert_random/BTreeSet  time:   [567.21 µs 569.21 µs 571.41 µs]
                        change: [-1.4789% -0.9567% -0.4730%] (p = 0.00 < 0.05)
                        Change within noise threshold.
Found 1 outliers among 100 measurements (1.00%)
  1 (1.00%) high mild

insert_reverse/RedBlackTree
                        time:   [990.29 µs 1.0019 ms 1.0130 ms]
                        change: [-20.555% -6.0816% +12.647%] (p = 0.56 > 0.05)
                        No change in performance detected.
Found 11 outliers among 100 measurements (11.00%)
  6 (6.00%) low severe
  1 (1.00%) low mild
  2 (2.00%) high mild
  2 (2.00%) high severe

insert_reverse/BTreeSet time:   [168.29 µs 169.40 µs 170.41 µs]
                        change: [-5.1385% -3.5285% -2.0641%] (p = 0.00 < 0.05)
                        Performance has improved.
Found 2 outliers among 100 measurements (2.00%)
  2 (2.00%) low mild

lookup_sequential/RedBlackTree
                        time:   [301.97 µs 304.62 µs 307.84 µs]
                        change: [-1.3359% -0.6104% +0.1694%] (p = 0.12 > 0.05)
                        No change in performance detected.
Found 3 outliers among 100 measurements (3.00%)
  1 (1.00%) high mild
  2 (2.00%) high severe

lookup_sequential/BTreeSet
                        time:   [311.80 µs 312.77 µs 313.72 µs]
                        change: [-1.1289% -0.6425% -0.1725%] (p = 0.01 < 0.05)
                        Change within noise threshold.

lookup_random/RedBlackTree
                        time:   [173.65 µs 177.56 µs 181.80 µs]
                        change: [+8.0793% +9.3521% +10.759%] (p = 0.00 < 0.05)
                        Performance has regressed.
Found 16 outliers among 100 measurements (16.00%)
  4 (4.00%) low mild
  3 (3.00%) high mild
  9 (9.00%) high severe

lookup_random/BTreeSet  time:   [218.26 µs 220.17 µs 222.59 µs]
Found 5 outliers among 100 measurements (5.00%)
  2 (2.00%) high mild
  3 (3.00%) high severe

mixed_operations/RedBlackTree
                        time:   [666.81 µs 673.84 µs 680.57 µs]
Found 13 outliers among 100 measurements (13.00%)
  7 (7.00%) low severe
  2 (2.00%) low mild
  2 (2.00%) high mild
  2 (2.00%) high severe

mixed_operations/BTreeSet
                        time:   [326.32 µs 326.90 µs 327.55 µs]
Found 5 outliers among 100 measurements (5.00%)
  3 (3.00%) high mild
  2 (2.00%) high severe

clear/RedBlackTree      time:   [55.129 µs 56.147 µs 57.346 µs]
Found 2 outliers among 100 measurements (2.00%)
  1 (1.00%) high mild
  1 (1.00%) high severe

clear/BTreeSet          time:   [35.183 µs 36.522 µs 37.988 µs]
Found 15 outliers among 100 measurements (15.00%)
  5 (5.00%) high mild
  10 (10.00%) high severe

duplicate_inserts/RedBlackTree
                        time:   [13.108 µs 13.863 µs 14.663 µs]
Found 1 outliers among 100 measurements (1.00%)
  1 (1.00%) high mild

duplicate_inserts/BTreeSet
                        time:   [24.393 µs 24.619 µs 24.850 µs]

size_scaling/RedBlackTree_insert/1000
                        time:   [94.322 µs 96.293 µs 98.255 µs]
Found 15 outliers among 100 measurements (15.00%)
  11 (11.00%) low mild
  1 (1.00%) high mild
  3 (3.00%) high severe

size_scaling/BTreeSet_insert/1000
                        time:   [28.646 µs 28.825 µs 29.013 µs]
Found 3 outliers among 100 measurements (3.00%)
  3 (3.00%) high mild

size_scaling/RedBlackTree_insert/5000
                        time:   [745.84 µs 757.19 µs 768.17 µs]
Found 14 outliers among 100 measurements (14.00%)
  7 (7.00%) low severe
  1 (1.00%) low mild
  2 (2.00%) high mild
  4 (4.00%) high severe

size_scaling/BTreeSet_insert/5000
                        time:   [199.01 µs 199.91 µs 200.78 µs]

size_scaling/RedBlackTree_insert/10000
                        time:   [1.6169 ms 1.6408 ms 1.6644 ms]
Found 13 outliers among 100 measurements (13.00%)
  6 (6.00%) low severe
  2 (2.00%) low mild
  2 (2.00%) high mild
  3 (3.00%) high severe

size_scaling/BTreeSet_insert/10000
                        time:   [426.67 µs 428.17 µs 429.78 µs]
Found 1 outliers among 100 measurements (1.00%)
  1 (1.00%) high mild

size_scaling/RedBlackTree_insert/25000
                        time:   [3.5540 ms 3.6302 ms 3.6967 ms]
Found 11 outliers among 100 measurements (11.00%)
  9 (9.00%) low severe
  2 (2.00%) high mild

size_scaling/BTreeSet_insert/25000
                        time:   [1.1261 ms 1.1297 ms 1.1331 ms]
Found 5 outliers among 100 measurements (5.00%)
  1 (1.00%) low mild
  2 (2.00%) high mild
  2 (2.00%) high severe
```

### Criterion Output Format

Each timing result shows `[lower_bound mean upper_bound]` with 95% confidence intervals:
- **Point estimate**: The most likely timing value (middle number)
- **Confidence interval**: The range where the true value likely falls
- **Change**: Performance change from previous runs (when available)
- **P-value**: Statistical significance of performance changes
- **Outliers**: Measurements outside normal distribution, categorized by severity

### Statistical Analysis Notes

- **Low/High Severe**: Measurements >3 standard deviations from mean
- **Low/High Mild**: Measurements 1.5-3 standard deviations from mean
- **P-value < 0.05**: Statistically significant change
- **Sample size**: 100 measurements per benchmark for robust statistics

