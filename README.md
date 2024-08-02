# :heavy_multiplication_x: Fast Windowed Multiplication implementation in Bitcoin

This repository contains the implementation of the Fast Multiplication algorithm in _Bitcoin_ for two 254-bit numbers using $w$-window multiplication. 

## :interrobang: How to test?

You can run all the tests by simply writing:

```bash
cargo test
```

However, more concretely, to verify the performance and the number of operations, you can run the following command. We also
specify where you can find the corresponding unit test in the project.

| Command | Description | Location |
| --- | --- | --- |
| `cargo test -- --nocapture test_254_bit_windowed_widening_optimized_mul` | Test our widening multiplication algorithm | [`test.rs`](src/bigint/arithmetics/test.rs#L641) |
| `cargo test -- --nocapture test_254_bit_narrow_mul_w_width` | Test our narrow multiplication algorithm | [`test.rs`](src/bigint/arithmetics/test.rs#L489) |
| `cargo test -- --nocapture test_254_bit_windowed_lazy_widening_mul` | Test _BitVM_'s widening multiplication algorithm (extended by us) | [`test.rs`](src/bigint/arithmetics/test.rs#L519) |
| `cargo test -- --nocapture test_254_bit_naive_widening_mul` | Test _BitVM_'s narrow multiplication algorithm (a bit optimized by us) | [`test.rs`](src/bigint/arithmetics/test.rs#L459) |
| `cargo test -- --nocapture test_255_bit_cmpeq_widening_mul` | Test [`cmpeq`](https://bitcointalk.org/index.php?topic=5477449.0)'s widening multiplication algorithm | [`test.rs`](src/bigint/cmpeq/test.rs#L56) |
| `cargo test -- --nocapture --ignored debug_mul_performance_comparison` | Compare the performance of several multiplication algorithms used | [`test.rs`](src/bigint/performance.rs#L14) |

## :zap: A few words about optimization

The two primary optimizations used are:

- Using the windowed method with `w=4` for multiplication.
- Improving the doubling step.

The windowed method is a well-known optimization for multiplication. It reduces the number of additions with an additional
cost to generate the lookup table. Namely, we use the base `1<<w` for the windowed method and based on the decomposition
coefficient `d` at each step, we add the corresponding value from the lookup table. The lookup table is generated by
precomputing the values of `d*z` for all `d` in the range `{0, 1, ..., 1<<w-1}` and given integer `z`. This way, we only have roughly
`b/(1<<w)` additions, where `b` is the number of bits in the number, while the number of doubling steps remains the same.

The doubling step was easy to optimize, though: we noticed that the original implementation was not optimal since
it implemented `double(a)` as `add(a, a)`. However, we can do better by not zipping the same number with itself, but
simply duplicating the limb at each step and carrying the overflow. This way, we can significantly reduce the number of operations
since the doubling step is used 254 times in the multiplication algorithm.
