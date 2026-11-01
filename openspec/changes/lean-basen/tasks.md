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

- [x] 4.1 Re-export all seven bases from the `BaseN` root (module re-exports
      only). **No facade, no `Base` inductive, no `encode (b : Base)`/
      `decode (b : Base)` dispatcher:** each base is its own `Codec` value,
      decoded/encoded by the single uniform `Codec.decode`/`Codec.encode`
      (`Codec.decodeFull hexElem …`, `decodeFullB64 s`, `encodeB32 bs`). The
      radix lives in the value the caller holds, never a dispatch index. The
      per-base roundtrip laws are the surface (`BaseN.Base{X}.roundtrip`, plus
      `decodeFullB64_roundtrip`/`decodeFullB32_roundtrip` for the padded bases).
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

- [x] 5.2 **AGENTS.md drift (in `../lean-basen/AGENTS.md`).** — **done.** The
      stale `Base`-enum bullet was not just out of date, it described a facade that
      **does not exist**: there is no `Base` inductive and no `BaseN.roundtrip`
      dispatch (`BaseN.lean` is module re-exports only, by design — task 4.1).
      Replaced with the seven-bases statement plus the honest "ledger lives in
      `lean-codec`" direction; the `basen-uniform-leaf-api` "Remaining: 3.6/3.7"
      section — an archived change — was replaced by the settled base32/64 shape
      note (kept, because a future edit to those two files still needs it).
- [x] 5.3 **`bench` executable not wired as a flake/default.nix target.** —
      **done.** `default.nix` gained a `bench` derivation (`targets = "bench"`,
      `mainProgram = "bench"`), `flake.nix` exposes `packages.bench`. Deliberate
      choice: it is a **package, not a `checks` entry** — the lane value-checks
      known vectors, which is evidence, not proof, and must not be able to fail the
      proof gate. Its `installPhase` **runs** the executable, so `nix build .#bench`
      verifies rather than merely producing a binary: the vectors are
      `example … := rfl`, so a wrong one is an elaboration error. Verified both
      ways this session — sandboxed `nix build .#packages.aarch64-darwin.bench`
      builds (45 jobs), runs, installs `bin/bench`, and exits 0; corrupting one
      hex vector to `[0x36, 0x37]` fails `lake build bench` with
      `has type ?m.13 = ?m.13 but is expected to have type
    Base16.hexBlockUnapply 102 = some [54, 55]`.
- [x] 5.4 **`lakefile.lean` pins `@ "master"` vs the template's `@ "main"`.** —
      **done.** Commented in `lakefile.lean` and cross-referenced from AGENTS.md.
      The finding's framing was wrong on one point worth recording: `master` is
      **not** a mistake here — it is this ecosystem's actual default branch (the
      template predates it), and the ref is a **floating dev-loop ref, not a pin**:
      `default.nix` rewrites the `require` to `./codec-src`, so a Nix build never
      reads that line and `flake.lock` is the only reproducibility anchor. Pinning
      it to a SHA would only make `lake build` fail after a lock bump.
- [x] 5.8 **Dead/redundant `have`s** in `BaseN/Base8.lean` & `BaseN/Base10.lean`. —
      **done, and the review's premise was partly wrong.** Nothing was "dead" in
      the sense of unused-by-name; the redundancy was _provable-inline_. Removed
      **six** `have`s (all re-`omega`-derivable from context, build re-verified):
      `hdiv64`/`hdiv8` in `oct_sum_eq`, `hdiv100`/`hdiv10` in `dig_sum_eq` (plain
      `omega` rediscovers `Nat.div_add_mod`), and `hmod`/`hmod'`/`hc8`/`hf8` in
      `oct_decompose_unique`'s two branches. **Refuted by experiment, not kept:**
      `hbv64`/`hbv8`/`hbv0` (`octBlockApply_unapply`) and `h0`/`h1`/`h2`
      (`digDigit_valid_of_byte`) are load-bearing — they feed `valToOct_lt_256` /
      `valToDig_lt_256` / `*_valid`; likewise the `hlen : m = 3` lemmas are
      load-bearing despite being consumed only through `omega` (removing them
      failed with `omega could not prove the goal ... a := ↑m`). Each removal was
      applied and built, so no claim here is by inspection alone.
- [x] 5.9 **`BaseN/Base2.lean` `valToBit` falls back to `49` for invalid input** —
      **done.** The docstring now states the asymmetry is **deliberate**: `bitVal`
      has an out-of-range `2` sentinel (so `bitValid`, defined as `bitVal e ≤ 1`,
      can detect it), while `valToBit` has no in-band sentinel — every `b ≠ 0` maps
      to `'1'`, so `valToBit 7 = valToBit 1`. Sound only because every proved use
      supplies `b ≤ 1`. Recorded why neither sentinel should be "harmonised": `2`
      is not a character and `48` would alias `b = 0`. `valToBit` itself depends on
      no axioms (checked).
- [x] 5.12 **`lake-manifest.json` (gitignored) vs `flake.lock` rev note** —
      **done.** AGENTS.md now has a short "Two files that look like they pin
      `codec` but do not" subsection: `lakefile.lean`'s git ref is the floating
      dev-loop ref and is rewritten by `default.nix`; `lake-manifest.json` is
      whatever the last local `lake update` wrote and drifts silently;
      `flake.lock`'s `nodes.codec.locked.rev` is the only anchor, and the one to
      check on a `bad import` from a sandboxed build.
- [x] 5.13 **Exported laws named `byte0`/`byte1`/… (bare lowercase)** in base32/64;
      rename to lowerCamelCase would be cleaner. — **done.** Renamed
      `byte0`…`byte4` → `byte0Of`…`byte4Of` (`Base32.lean`, 5 lemmas) and
      `byte0`…`byte2` → `byte0Of`…`byte2Of` (`Base64.lean`, 3 lemmas), with every
      call site and docstring. No external references existed (`grep` across both
      repos). All eight are `[propext, Quot.sound]`-only (checked, not assumed),
      both `roundtrip` laws still are, and the AGENTS.md base32/64 note now uses
      the `Of` names so a future edit does not reintroduce the bare ones.

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
