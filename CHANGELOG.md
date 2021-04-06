## 1.0.1.0 [2021-05-06]
- Fixed a critical bug in certain values in `Dictionaries` that could cause segfaults.
- Reimplemented and simplified `Subset`.
- Adjusted basic type families to better handle simple cases (affected families are `.\`, `Extend`, `.+`, `.\/`, `.//`).
- Export `mapSingleA` in `Data.Row.Variants`.
- Improved kind polymorphism and simplify a few constraints ([Thanks Strake!](https://github.com/target/row-types/pull/73)).
- Improved type checking performance ([Thanks UlfNorell!](https://github.com/target/row-types/pull/71))


## 1.0.0.0 [2020-09-12]
This release has many breaking changes, specifically to `metamorph` and some functions related to `Variant`, hence the major version bump to `1.0`.  However, users that only use basic features of records may not notice a difference.

- Removed `metamorph'` and `biMetamorph'` in favor of generalizing `metamorph` over choice of bifunctor.
- Removed "unsafe" functions (`unsafeRemove` and `unsafeInjectFront` from `Records` and `unsafeMarkVar` and `unsafeInjectFront` from `Variants`).
- Removed `Switch` class, reimplementing the `switch` function using `BiForall`.
- Swap the order of the result of calling `trial`, `multiTrial`, and `split`.
- Added new functions to `Records`: `lazyRemove`, `curryRec`, `(.$)`, `zipTransform`, `zipTransform'`, `traverse`, `traverseMap`, `distribute`, and `coerceRec`.
- Added new functions to `Variants`: `fromLabelsMap`, `traverse`, `traverseMap`, and `coerceVar`.
- Added `Dictionaries` module, full of axioms that are helpful for using `metamorph`.  Moved axioms from `Internal` to `Dictionaries` (in some cases, the type variable order has changed).
- Added `ApSingle` type family as well as `eraseSingle`, `mapSingle`, and `eraseZipSingle` (thanks Jordan Woehr!).
- Improved error messages.

Note: GHC 8.4 and earlier are no longer officially supported in row-types 1.0.0.0.


## 0.4.0.0 [2020-05-20]
- Renamed `toNative` to `toNativeGeneral` and `toNativeExact` to `toNative` for records and likewise for `fromNative` for variants.
- Added a type family `NativeRow` which, when given any generic type that can go through `fromNative`, is equal to the row-type of the resulting record/variant.  Note that `NativeRow` is defined separately (and differently!) for records vs variants, so it is exported at the `Data.Row.Records`/`Variants` level but not at `Data.Row`.
- Added `coerceRec` and `coerceVar` to coerce the row-types of records and variants respectively.
- Exposed `BiForall` in `Data.Row`, `Data.Row.Records`, and `Data.Row.Variants`
- (Internal) Rewrote internal `Generic` code to use an associated type family instead of a standalone one.

Note: GHC 8.2 and earlier are no longer officially supported in row-types 0.4.0.0.

## 0.3.1.0 [2020-01-29]
- Added "native" classes as exports for `Records` and `Variants` (e.g., `ToNative`, `FromNative`)
- Added more example hs files.

## 0.3.0.0 [2019-05-28]
- Added `HasField` and `AsConstructor` instances (from generic-lens) for `Rec` and `Var` respectively.
- Added record-overwrite function `.//`.
- Added `Generic` instances for Rec and Var.
- Added mapHas entailment connecting `Map f r .! l` to `r .! l`.
- Changed `Forall2` to `BiForall`.
  - Added `BiConstraint` type class for use  with `BiForall`.
- Added `Ap` type family that functions as `ap` over rows using zipping.
  - Added `mapF` to map a function over a record with an `Ap` row.
- Added `toDynamicMap` and `fromDynamicMap` as functions to convert between `Rec`s and  `HashMap Text Dynamic`s.
- Added `toNativeExact` to convert a `Rec` to a native Haskell type without losing any fields.
- Added `toNative`, `fromNative`, and `fromNativeExact` for `Var`s.
- Added `unSingleton` for `Var`s.
  - Removed `unSingleton` from `Data.Row` export list.
- Tightened the type signatures of `focus` (for both `Rec` and `Var`) to improve type inference when using `focus` in lens-like situations.

## 0.2.3.1 [2018-07-11]
- Fix a bug in the `Show` instance for `Rec`.

## 0.2.3.0 [2018-07-02]
- Update the `Show` instance for `Rec` to render valid code.
- Add `toNative` and `fromNative` functions for records to easily convert between Haskell records and row-types records.
- Make type families in `Data.Row.Internal` polykinded (thanks James Yu!)

## 0.2.1.0 [2018-03-20]
- Bug Fix: The type of `update` for both `Rec` and `Var` now enforce the newly inserted type is correct.
- New: Add `restrict` and `split` for `Var`s.  
  - Removed `restrict` from `Data.Row` export list.
- New: Added support for universally quantified rows: `mapForall` and `uniqueMap`.
- Added very simple test suite.

## 0.2.0.0 [2018-02-12]
- Initial Release
