![test workflow](https://github.com/DATP7/radguy/actions/workflows/rust.yml/badge.svg)
![format workflow](https://github.com/DATP7/radguy/actions/workflows/format.yml/badge.svg)

# Radguy 
Abstract dependency graphs without dependency graphs (in rust!🦀)

# Running
This program requires Rust version `nightly-2025-04-27`. With [rustup](https://rustup.rs/) correctly installed, it can be built using
```sh
cargo build
```
Iteration experiments can be run using
```sh
cargo run --release --features timeout
```
Benchmarks can be run with
```sh
cargo bench --features timeout
```
