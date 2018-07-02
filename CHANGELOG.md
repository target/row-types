
## 0.2.3.0 [2018-07-02]
- Update the Show instance to render valid code.
- Add 'toNative' and 'fromNative' functions for records to easily convert between Haskell records and row-types records.
- Make type families in Data.Row.Internal polykinded (thanks James Yu!)

## 0.2.1.0 [2018-03-20]
- Bug Fix: The type of 'update' for both Record and Variant now enforce the newly inserted type is correct.
- New: Add 'restrict' and 'split' for Variants.  
- - Removed 'restrict' from Data.Row export list.
- New: Added support for universally quantified rows: 'mapForall' and 'uniqueMap'.
- Added very simple test suite.

## 0.2.0.0 [2018-02-12]
- Initial Release
