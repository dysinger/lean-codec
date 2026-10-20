# Tasks

## 1. Scaffold lean-basen from the template

- [x] 1.1 `git init` `lean-basen` from `lean-nix-flake-template`; rename package
      `demo` → `basen`, module `Example` → `BaseN`; wire `require codec from git`
      (flake input `codec-src` + `codec-native` `.olean` artifacts per the
      `ecosystem` dependency-injection convention) and verify `lake build` on the
      renamed skeleton passes
- [x] 1.2 Add the `BaseN` module skeleton (facade + empty `BaseN.Base2/4/8/10/16/32/64`)
      with `lakefile.lean` roots set, and verify `lake build`

## 2. Port the four RFC 4648 bases (08/16/32/64)

- [x] 2.1 Port `Data.BaseN.Base16` to `BaseN.Base16` (alphabet `0-9A-F`, uppercase,
      no padding): `encode_base16`/`decode_base16` + `lemma_base16_roundtrip`, and
      verify `#eval` byte-exact against RFC 4648 §10 (`""→""`, `"f"→"66"`,
      `"fo"→"666F"`, `"foo"→"666F6F"`, `"foob"→"666F6F62"`, `"fooba"→"666F6F6261"`,
      `"foobar"→"666F6F626172"`) — vectors corrected to RFC 4648 uppercase
- [x] 2.2 Port `Data.BaseN.Base08` to `BaseN.Base8` (octal, 3 digits/byte) +
      roundtrip, and verify byte-exact against hand vectors
- [x] 2.3 Port `Data.BaseN.Base32` to `BaseN.Base32` (`A-Z2-7`, `=` padding) +
      roundtrip, verify against RFC 4648 §10 (`""→""`, `"f"→"MY======"`,
      `"fo"→"MZXQ===="`, `"foo"→"MZXW6==="`, `"foob"→"MZXW6YQ="`,
      `"fooba"→"MZXW6YTB"`, `"foobar"→"MZXW6YTBOI======"`)
- [x] 2.4 Port `Data.BaseN.Base64` to `BaseN.Base64` (`A-Za-z0-9+/`, `=` padding) +
      roundtrip, verify against RFC 4648 §10 (`""→""`, `"f"→"Zg=="`, `"fo"→"Zm8="`,
      `"foo"→"Zm9v"`, `"foob"→"Zm9vYg=="`, `"fooba"→"Zm9vYmE="`,
      `"foobar"→"Zm9vYmFy"`)

## 3. Add Base2, Base4, Base10 (new semantics)

- [x] 3.1 Define + implement `BaseN.Base2` (one bit per `0`/`1` char, 8 chars per
      byte, MSB-first) + roundtrip; verify byte-exact against hand vectors
- [x] 3.2 Define + implement `BaseN.Base4` (one quartet per `0-3` char, 4 chars
      per byte) + roundtrip; verify byte-exact against hand vectors
- [x] 3.3 Define + implement `BaseN.Base10` (decimal digit math, byte-oriented,
      no sign) + roundtrip; verify byte-exact against hand vectors

## 4. Facade, bench lane, and gate

- [x] 4.1 Add the `BaseN` facade re-exporting all seven bases + an inductive
      `Base := B2 | B4 | B8 | B10 | B16 | B32 | B64` (module re-exports only —
      **no** `roundtrip` dispatch theorem; the bespoke facade `roundtrip` was
      removed in `basen-uniform-leaf-api`, and the per-base `roundtrip` laws are
      the surface, each `BaseN.Base{X}.roundtrip`)
- [x] 4.2 Add a bench lane value-checking each base byte-for-byte (RFC 4648 §10
      for 16/32/64, hand vectors for 2/4/8/10) and the roundtrip laws
- [x] 4.3 Gate: `lake build` zero `sorry`/warnings; `#print axioms` on each
      per-base `BaseN.Base{X}.roundtrip` reports only `[propext, Quot.sound]`;
      `nix flake check` green; commit + push `lean-basen`
      — **done (this session)**: the flake-injection half of 1.1 is landed in
      `lean-basen` (commit `9bdfd4b`, pushed). `codec` is a flake input
      (`github:dysinger/lean-codec`, the correct shorthand) threaded as
      `codecSrc` into `default.nix`, which copies the source into the writable
      sandbox and rewrites `require codec from git …` → `require codec from
"./codec-src"`, so `lake build` builds codec from source with **no
      `git clone`/network**. `lake build` zero sorry/warnings; `#print axioms` on
      every per-base `BaseN.Base{X}.roundtrip` = `[propext, Quot.sound]`;
      `nix flake check` green (both `checks.lean` and
      `checks.formatting`).

**Caveat resolved (this session):** `lean-codec` was **private**, which meant
fetching the `github:` input needed `access-tokens = github.com=<token>` in
`nix.conf` (no `--impure`, but a credential). The repo is now **public**, so
`nix flake check` runs green with a plain invocation — no token, no
`--impure`, fully portable.

## 5. Review findings (hypercritical review, 2026-10-18; re-classified 2026-10-20)

Recorded verbatim from the full review (`/tmp/lean-basen-review.md`); nothing is
"too minor" to track. **Re-classification after `basen-uniform-leaf-api`:** the
`Codec`-value rewrite deleted the bespoke `decodeN`/`decode`/`encode` surface
that most of these findings reference. Status below reflects the current surface;
findings marked **superseded** are re-derived in
`basen-rfc-conformance-theorems` (the active change), not in this one.

### Superseded — re-derived in `basen-rfc-conformance-theorems`

- [x] 5.1 **RFC 4648 non-conformance: base32/base64 decoders accept trailing data
      after `=` padding (padding is not enforced to be terminal).** — the bespoke
      `decodeN`/`decode` tail branches no longer exist; the block `iso` in
      `b32BlockApply`/`b64BlockApply` enforces intra-block canonicality. The
      **run-level** terminal-padding property (a `=`-terminated block followed by
      data) is now `basen-rfc-conformance-theorems` task 1.x. _(History: commit
      `bb46230` in `../lean-basen` attempted a **post-hoc filter**
      `decodeB64Strict = decodeFull; if b64TerminalPad bs …` and a rejection
      theorem assuming `hf : decodeFull … = some …`; that approach was re-evaluated
      as the design's rejected "mechanism 3" and is superseded by the structural
      split-grammar plan — see `basen-rfc-conformance-theorems` design D3/task 1.1a.)_
- [x] 5.7 **`smoke` (runtime) covers only base32/base64, not all seven bases.** —
      the rewrite removed the runtime `smoke`; the bench lane now value-checks all
      seven at the block `iso` level. The rejection-class vectors moved to
      `basen-rfc-conformance-theorems` task 5.1.
- [x] 5.10 **Base16 case-insensitive decode is untested.** — recorded as an
      **explicit non-goal** in `basen-rfc-conformance-theorems` (design D8): the
      `Codec`-value `hexElem` is uppercase-only by design, and a
      case-insensitive decoder is not a strict `Iso`. The lowercase `6f` case is
      covered there as a _rejection_ (uppercase-only), not an accepted alias.

### Moot after `basen-uniform-leaf-api`

- [x] 5.5 **`#eval`/`#check` diagnostics leak into the build log.** — the rewritten
      `Bench.lean` uses only `example … := rfl`; no `#check`/`#eval` remain.
- [x] 5.6 **Bench.lean module doc says "closed by `decide`/`rfl`".** — the
      rewritten module doc no longer overstates the automation.
- [x] 5.11 **Base32/Base64 `roundtrip` near-verbatim re-derivation of
      `roundtripN`.** — the `Codec`-value rewrite replaced the bespoke `roundtrip`
      with the inherited `roundtrip`, so the duplicated surface is gone.

### Still open — mechanical polish (in `lean-basen`, not RFC-conformance)

- [ ] 5.2 **AGENTS.md drift (in `../lean-basen/AGENTS.md`).** The doc still says
      the facade `Base` is "currently scoped to B2/B4/B8/B10/B16; B32/B64 are in
      progress" and "`Base32.lean`/`Base64.lean` are the remaining work — tasks
      3.6/3.7." Both are stale (all seven bases landed). Fix the two bullets, and
      the "Active work: `basen-uniform-leaf-api`" section's "Remaining" line.
- [ ] 5.3 **`bench` executable not wired as a flake/default.nix target.**
      `lakefile.lean` declares `lean_exe bench`, but `flake.nix` has no
      `packages.bench` and `default.nix` has no `bench` target (`nix build .#bench`
      fails). Add it or document as dev-loop-only.
- [ ] 5.4 **`lakefile.lean` pins `@ "master"` vs the template's `@ "main"`.**
      Undocumented and a floating ref outside the pinned flake. Comment it.
- [ ] 5.8 **Dead/redundant `have`s** in `BaseN/Base8.lean` & `BaseN/Base10.lean`.
- [ ] 5.9 **`BaseN/Base2.lean` `valToBit` falls back to `49` for invalid input** —
      a doc note on the asymmetry with `bitVal`'s `2` sentinel.
- [ ] 5.12 **`lake-manifest.json` (gitignored) vs `flake.lock` rev note** — one-line
      AGENTS.md note.
- [ ] 5.13 **Exported laws named `byte0`/`byte1`/… (bare lowercase)** in base32/64;
      rename to lowerCamelCase would be cleaner.

## Status (re-anchored 2026-10-20): this change is complete except mechanical polish

The substantive work (seven `Codec`-value bases + facade + bench + gate) is **done**
and landed (`basen-uniform-leaf-api`, archived; lean-basen commits
`7eefebc`…`bef44ae`). `lake build` green, zero `sorry`/warnings, every per-base
`roundtrip` `[propext, Quot.sound]`-only, `nix flake check` green.

**Remaining here: only 5.2/5.3/5.4/5.8/5.9/5.12/5.13** — seven mechanical polish
items in `../lean-basen` (no proofs). The substantive RFC conformance work
(rejection, canonical form, converse/injectivity) lives in
**`basen-rfc-conformance-theorems`**, the active change.

Do the polish items in dependency order: 5.2 (AGENTS.md, unblocks correct context)
→ 5.3/5.4/5.12 (build wiring + notes) → 5.8/5.9/5.13 (code/doc nits).
