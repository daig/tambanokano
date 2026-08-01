# TODO

## Re-home deleted META boundary coverage

The removed `conformance/probes/meta-recognized-boundaries.maude` fixture covered META operations that are not all represented by retained tests. Add permanent behavior-level coverage for:

- [ ] proper-residue `metaXmatch` and `metaXapply`;
- [ ] partial-AC whole-pattern `metaXmatch` and `metaXapply`, including bindings, values, and contexts;
- [ ] conditioned `metaMatch` and `metaXmatch`;
- [ ] conditional-rule `metaApply` and `metaXapply`;
- [ ] `metaParseStrategy` and `metaPrettyPrintStrategy`;
- [ ] `upModule` and literal reflected-module memo attributes.

Preserve the observed TNK boundary, not merely successful cases: supported operations must keep their pinned results, while unsupported operations must remain recoverable and unreduced rather than being mis-evaluated. Cover the public `Session` or REPL path. Where differential probing established the original baseline, retain that output only as historical provenance, not as an ongoing compatibility requirement.
