# simulacrum

An Ethereum transaction simulator in Rust using the latest (at the time of
writing) versions of `revm` and `alloy`.

This project was inspired by [simular-core](https://github.com/simular-fi/simular-core/).

## Progress

- [x] Simple ETH transfers
- [ ] Arbitrary contract calls
- [ ] Arbitrary transaction execution
- [ ] ERC20 balance queries, approvals, and transfers (convenience functions)
- [ ] Documentation (see `src/lib.rs` for now)

## Quick start

Clone this repository and run:

```bash
cargo test
```
