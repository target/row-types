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
