# SmallStr

A `String`-like but using `SmallVec` internally

- `SmallStr<N>` == `SmallVec<u8, N>`
- `Clone` is `O(n)`
- Strings smaller than `N` bytes are allocated on the stack.
- `SmallString` is an alias for `SmallStr<16>` and `size_of::<SmallString>() == size_of::<String>()` on 64-bit platform

## Macro
macro `format_smallstr!` like `format!`

## Traits
`ToSmallStr` like `ToString`, convert `T: Display` to `SmallStr`
```
pub trait ToSmallStr {
    fn to_smallstr<const N: usize>(&self) -> SmallStr<N>;
}
```