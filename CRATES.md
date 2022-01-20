Provides mappable `Rc` and `Arc` types.

```rust
use mappable_rc::Mrc;

let m: Mrc<[u32]> = vec![1, 2, 3, 4].into();
assert_eq!(m.as_ref(), &[1, 2, 3, 4]);

let m: Mrc<[u32]> = Mrc::map(m, |slice| &slice[1..=2]);
assert_eq!(m.as_ref(), &[2, 3]);
```