# :heavy_multiplication_x: Fast Multiplication implementation in Bitcoin

This repository contains the implementation of the Fast Multiplication algorithm in Bitcoin for two
254-bit numbers.

## How to test?

You can run all the tests by simply writing:

```bash
cargo test
```

However, more concretely, to verify the performance and the number of operations, you can run the following command. We also
specify where you can find the corresponding unit test in the project.

| Command | Description | Location |
| --- | --- | --- |
| `cargo test -- --nocapture test_254_bit_windowed_widening_mul` | Test our widening multiplication algorithm | [`test.rs`](src/bigint/arithmetics/test.rs#L517) |
| `cargo test -- --nocapture test_mul_w_width_254bit` | Test our narrow multiplication algorithm | [`test.rs`](src/bigint/arithmetics/test.rs#L487) |
| `cargo test -- --nocapture test_254_bit_widening_mul` | Test _BitVM_'s widening multiplication algorithm (extended by us) | src/bigint/arithmetics/test.rs#L457 |
| `cargo test -- --nocapture test_64_and_254_bit_mul` | Test _BitVM_'s narrow multiplication algorithm (a bit optimized by us) | src/bigint/arithmetics/test.rs#L414 |
| `cargo test -- --nocapture test_255_bit_cmpeq_widening_mul` | Test `cmpeq`'s widening multiplication algorithm | [`test.rs`](src/bigint/cmpeq/test.rs#L56) |
| `cargo test -- --nocapture --ignored debug_mul_performance_comparison` | Compare the performance of several multiplication algorithms used | [`test.rs`](src/bigint/performance.rs#L14) |
