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
      `Base := B2 | B4 | B8 | B10 | B16 | B32 | B64` and a single `roundtrip` theorem
      dispatching to the per-base lemmas (proved by `cases`)
- [x] 4.2 Add a bench lane value-checking each base byte-for-byte (RFC 4648 §10
      for 16/32/64, hand vectors for 2/4/8/10) and the roundtrip laws
- [x] 4.3 Gate: `lake build` zero `sorry`/warnings; `#print axioms` on
      `BaseN.roundtrip` (and each `lemma_baseX_roundtrip`) reports only
      `[propext, Quot.sound]`; `nix flake check` green; commit + push `lean-basen`
      — **done (this session)**: the flake-injection half of 1.1 is landed in
      `lean-basen` (commit `9bdfd4b`, pushed). `codec` is a flake input
      (`github:dysinger/lean-codec`, the correct shorthand) threaded as
      `codecSrc` into `default.nix`, which copies the source into the writable
      sandbox and rewrites `require codec from git …` → `require codec from
"./codec-src"`, so `lake build` builds codec from source with **no
      `git clone`/network**. `lake build` zero sorry/warnings; `#print axioms
BaseN.roundtrip` + every `BaseN.Base{X}.roundtrip` = `[propext,
Quot.sound]`; `nix flake check` green (both `checks.lean` and
      `checks.formatting`).

**Caveat resolved (this session):** `lean-codec` was **private**, which meant
fetching the `github:` input needed `access-tokens = github.com=<token>` in
`nix.conf` (no `--impure`, but a credential). The repo is now **public**, so
`nix flake check` runs green with a plain invocation — no token, no
`--impure`, fully portable.

## 5. Review findings (hypercritical review, 2026-10-18; all open)

Recorded verbatim from the full review (`/tmp/lean-basen-review.md`); nothing is
"too minor" to track.

### Warnings

- [ ] 5.1 **RFC 4648 non-conformance: base32/base64 decoders accept trailing data
      after `=` padding (padding is not enforced to be terminal).**
      `BaseN/Base32.lean` (`decodeN` ~190, `decode` ~545) and `BaseN/Base64.lean`
      (`decodeN` ~190, `decode` ~400): the padded-tail branches `match decodeN
    rest` / `match decode rest` recursively decode _whatever remains_ after the
      `=` group, with no check that `rest = []`. Roundtrip is unaffected (the
      encoder never emits this), so it is a _correctness-of-rejection_ gap. Fix:
      in each padded-tail branch, guard `rest = []` (decode only pads at the _whole
      string_ boundary).
- [ ] 5.2 **AGENTS.md doc drift — describes the project as half-finished.** "Map
      of the repo" says `inductive Base` is "currently scoped to B2/B4/B8/B10/B16;
      B32/B64 are in progress" and "(`Base32.lean`/`Base64.lean` are the remaining
      work — tasks 2.3/2.4.)" — but all seven bases are landed and proved. Fix the
      two stale bullets.
- [ ] 5.3 **`bench` executable not wired into the flake as a `bench` package
      (deviation from `codec`).** `lakefile.lean` declares `lean_exe bench`, but
      `flake.nix` has no `packages.bench` and `default.nix` has no `bench` target
      (codec has both). `nix build .#bench` doesn't exist. Add
      `packages.bench = _pkg.bench;` + a `bench = mkLakeBuild { targets = "bench";
    mainProgram = "bench"; … }` in `default.nix`, or document it as dev-loop-only.
- [ ] 5.4 **`lakefile.lean` pins codec at `@ "master"`; template documents `@ "main"`.**
      `master` is correct today (codec's default branch), but the deviation is
      undocumented and a floating branch ref is non-reproducible outside the pinned
      flake. Comment it or sync the template text.
- [ ] 5.5 **`#eval`/`#check` diagnostics leak into the build log**
      (`Bench.lean` ~91–97, 107): 7 `info:` + 1 `info: true` lines on every
      `lake build bench`. Harmless, but noisy; the `#check`s only typecheck and the
      `example` theorems already prove the dispatch.
- [ ] 5.6 **Bench.lean module doc says "closed by `decide`/`rfl`" but every vector
      is `rfl` only** — the docstring overstates the automation used.
- [ ] 5.7 **`smoke` (runtime) covers only base32/base64 (+ base64 partial), not all
      seven bases.** Compile-time `example` theorems cover all seven (sound), but the
      runtime `main` only exercises a subset.

### Suggestions

- [ ] 5.8 **Dead/redundant `have`s** in `BaseN/Base8.lean` & `BaseN/Base10.lean`
      (`hle` + duplicate `hle'` both unused; `octToVal_valToOct`'s unused `hd0`).
- [ ] 5.9 **`BaseN/Base2.lean` `valToBit` falls back to `49` (`'1'`)** for invalid
      input — asymmetric with `bitVal`'s `2` sentinel; worth a doc note.
- [ ] 5.10 **Base16 case-insensitive decode is untested** (works — `decode "6f" = some
    [111]`); add a lowercase vector to `Bench.lean`.
- [ ] 5.11 **Base32/Base64 UInt8 `roundtrip` is ~160/~150 lines of near-verbatim
      re-derivation of `roundtripN`** — a future transport-lemma refactor could cut
      2× the surface.
- [ ] 5.12 **`lake-manifest.json` (gitignored) pins a different `codec` rev than
      `flake.lock`** — expected, but a one-line AGENTS.md note would pre-empt confusion.

### Idiomatic-Lean minor items

- [ ] 5.13 **Exported laws named `byte0`/`byte1`/`byte2`/`byte3`/`byte4`** (bare
      lowercase, not lowerCamelCase), and base64 shadows base32's `byte0`/`byte1`
      within separate namespaces — no collision, but terse/conflicting for exported laws.
