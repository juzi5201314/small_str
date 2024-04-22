# SmallStr

A `String`-like but using `SmallVec` internally

- `SmallStr<N>` == `SmallVec<u8, N>`
- `Clone` is `O(n)`
- Strings smaller than `N` bytes are allocated on the stack.
- `SmallString` is an alias for `SmallStr<16>` and `size_of::<SmallString>() == size_of::<String>()` on 64-bit platform
