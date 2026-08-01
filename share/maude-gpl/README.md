# Maude companion libraries (GPLv2-or-later)

This directory redistributes stock Maude 3 library sources from SRI
International so tambanokano can `load` the same declaration files the
reference system ships.

| File | Provides |
|------|----------|
| `smt.maude` | SMT theory surface |
| `model-checker.maude` | LTL / model-checker surface |
| `metaInterpreter.maude` | META-INTERPRETER object protocol |

## License

**GNU GPL v2 or later.** See `COPYING` and the copyright header in each file.
These files are **not** covered by the repository-root MIT license.

## Use

Put this directory on `$MAUDE_LIB` (before or after your Maude prelude dir):

```sh
export MAUDE_LIB="$PWD/share/maude-gpl:$PWD/share/tnk:/path/to/maude/Main"
```

Fixtures and the differential harness expect that layout. You may delete or
omit this directory and supply equivalent stock files from a Maude install
instead.
