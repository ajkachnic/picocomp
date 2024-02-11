# picocomp

tiny expression compiler in Rust. compiles math expressions (ie. `(2 * 3) / 1 + 5`) to x86-64 assembly, targeting linux and intel syntax. ~400 lines of code

## usage

don't.

#### but seriously...

```sh
cargo run > test.s
make run # run the assembler and execute the result
```
