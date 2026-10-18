# Design

## Context

See `proposal.md` — Why. The Lean `codec` core is done (verified `Bytes n`
substrate + `Iso`/`Rel`/backtracking `decode`/partial `encode` + `[propext,
Quot.sound]`-only laws). The F* stack already exists as a proven layered set, so
the port is a _re-derivation_ in Lean of semantics we can read off the F* sources
and the xeno monorepo, not a green design.

Two load-bearing facts from prior work shape everything below:

1. **Pure-Lean parsing has a ~20–40×-off-C ceiling** (boxed `Nat`/`UInt8`/
   `UInt64` arithmetic in Lean 4.34.1's C backend; `USize` is the only raw
   scalar, and only as an `@[extern]` argument). The accepted decision: **all
   codecs stay pure Lean; C is only the generic bulk byte-movement seams**
   (`byteSlice`/`blitBytes`/`findByte`/`commitRemainder`); TLS crypto is FFI'd
   (OpenSSL/hacl), never re-proved.
2. The **Layer-2 trust seam** (`@[extern]` + a `.c` file) is invisible to Lean —
   `#print axioms` sees only the Lean elaborating body, so `[propext,
Quot.sound]`-cleanliness is a _runtime contract documented in prose_, not a
   proof step. Every package carries this posture forward.

## Goals / Non-Goals

**Goals:**

- Reproduce the F*/xeno dependency layering in Lean, one package per repo, from
  a single trusted template (`lean-nix-flake-template`).
- Split **variable-length binary** (`vbin`) and **text** (`text`) out of
  `codec` core — the two departures the user fixed in the request.
- Keep each package's _provability gate_ before volume: every law `[propext,
Quot.sound]`-only, zero `sorry`, `#print axioms` as the check.

**Non-Goals:**

- No change to `codec` core (`Codec.*`, `Bytes n`, laws stay untouched).
- No per-format C, no C that parses digits/fields, no re-proving crypto.
- No mathlib; stdlib-only, matching `codec`.
- No monorepo (the xeno model) — sibling repos following `fstar-*`.

## Decisions

### D1 — Package naming: `vbin`, internal names drop `lean-`

Git repo `lean-<name>`, internal `pname`/module = `<name>`. The varint package
is `vbin` (repo `lean-vbin`), matching the F* convention (`fstar-basen` →
`basen`) and reconciling the user's explicit "vbin, not varbinary". The F*
stack kept `varint` _inside_ `Data.Codec.Types`; we deliberately move it out
(already decided in `codec`: "VarBinary removed from core — LEB128 belongs in a
downstream package").

_Alternative considered:_ one `lean-varbinary`/`varbinary` name — rejected by the
user's explicit instruction and the already-committed core removal.

### D2 — The fixed dependency order

```
codec
 ├─ vbin   (LEB128 varint)
 ├─ basen    (Base2/4/8/10/16/32/64 — adds 2/4/10 over F*'s 08/16/32/64)
 ├─ text     (RFC 3629 UTF-8)
 ├─ proto    (protobuf: tags + varint fields + length-delimited)   → codec + vbin
 ├─ ip       (IPv4/IPv6)                                          → codec + basen
 ├─ dns      (RFC 1034/1035 variable-length names)                → codec + text
 ├─ uri      (RFC 3986)                                           → codec + text + basen + ip + dns
 ├─ (image, stm, xml, uuid, mime)                               → as F*
 ├─ http                                                          → codec + image + stm + text + uri + dns + ip
 └─ tls                                                            → codec + stm + FFI crypto
```

The order mirrors xeno `flake.nix:443-462` exactly (`dns` before `uri`, `http`
last, `tls` FFI-not-re-proved), plus the two fixes from the user: `vbin`
split out, `text` split out, and `proto` slotted on top of `vbin`.

### D3 — `proto` sits on `vbin`, not `codec`

Protobuf's wire format is tag-byte + LEB128 varint fields; the natural Lean
dependency is `proto` → `vbin` (reusing the one varint codec) rather than
re-deriving varint inside `proto`. This is the concrete reason `vbin` is its
own package: it is the shared primitive that `proto` (and any other length-
framed binary format) consumes.

### D4 — Dependency injection (flake inputs + `require from git`)

Each package pulls a dependency's **source dir** + **pre-built `.olean`** as a
flake input, then hands them to `default.nix` by named argument; the no-flakes
dev loop uses Lake `require … from git`. The `lean-nix-flake-template` README
already sketches both. This mirrors F*'s `codec-src = fstar-codec;
codec-checked = fstar-codec.packages.${system}.checked;`.

_Alternative considered:_ a single monorepo flake (the xeno model) — rejected to
match the established `fstar-*` sibling-repo convention and keep `#print axioms`
gates per-package.

### D5 — The substrate and proof discipline are inherited per-package

Every downstream package keeps `Bytes n` as its single spec substrate, stays
`[propext, Quot.sound]`-only, and inherits the Layer-2 trust-seam contract from
`codec` (a runtime contract in prose, excluded from the axiom gate). No package
introduces a `Classical.choice` or a second carrier.

## Risks / Trade-offs

- _*[Base2/4/10 are new (not in F*)]_* → their semantics are our own; define
  them precisely in each package's spec (bit-order, padding, digit-math) before
  coding, and cross-check against the DNSSEC/RFC base32hex and RFC 4648
  references where they exist.
- **[Base10 digit math is the boxed-arithmetic hotspot]** → accepted (pure-Lean
  stays ~20–40× off C; it is a parsing primitive, not a bulk-move seam).
- **[`text`/`vbin` "split" could drift back into `codec`]** → enforced by the
  `ecosystem` spec's "separate packages" requirement and the review gate.
- **[`proto` re-deriving varint instead of importing `vbin`]** → enforced by
  the ordering rule (`proto` → `vbin`, never `proto` → a private copy).
- **[Each repo must not regress the proven `codec` core]** → `codec` is a fixed
  input (flake-pinned git rev); no downstream package edits `Codec.*`.

## Migration Plan

1. `lean-nix-flake-template` exists and is verified (built this session).
2. For each package in ordering order: `git init` from the template, `require`
   the dependencies, port the corresponding F* modules to Lean, prove the laws
   `[propext, Quot.sound]`-only, gate with `lake build` + `#print axioms`, and
   publish.
3. `vbin` first (it unblocks `proto`); `text` early (it unblocks many);
   `http` last; `tls` after, with crypto FFI'd.

## Open Questions

- Whether to also port `json`/`yaml`/`toml`/`sql`/`cypher`/`uml` (present in the
  xeno monorepo but not yet extracted to `fstar-*` repos) before `http` — the
  user's stack named only `vbin`/`protobufs`/`unicode`/`base-N`/`http`/`tls`,
  so these are deferred, not dropped.
- Whether `unicode` in the user's list maps to the `text` (UTF-8) package or to a
  broader code-point/`String` normalization layer — deferred until `text` lands.
