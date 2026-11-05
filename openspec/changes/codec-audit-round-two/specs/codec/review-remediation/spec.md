# codec/review-remediation Specification (delta)

## MODIFIED Requirements

### Requirement: The proof gate SHALL be enforced, not observed

The repository SHALL fail its build when a proof is incomplete. A `sorry` in any
library source SHALL cause the `check` gate to fail; the gate SHALL NOT rely on a
human noticing a compiler warning. Because `lake build` reports `sorry` as a
warning rather than an error, the gate SHALL add an explicit enforcement step
(turning warnings into errors, or scanning the sources for `sorry`/`admit`) and
SHALL be documented as _enforced_ only once that step exists. Documentation SHALL
NOT describe an invariant as "the proof gate" when the build does not check it.

The gate's axiom check SHALL be runnable inside this repository. A documented
`#print axioms` example SHALL name a `lean-codec` declaration and be executable
here, not only in a downstream repository.

The **axiom half** of this gate SHALL be enforced on every build, not merely
runnable by hand. `#print axioms` being available to a reader does not satisfy this
requirement: a law whose footprint drifted to include `Classical.choice` would go
unnoticed until someone chose to check it. The repository SHALL therefore gate the
footprint of every public theorem automatically (see the `codec/axiom-gate`
capability), and SHALL NOT describe a law's axiom footprint in prose unless that
prose matches what the gate measures. Where a law is knowingly excluded from the
`[propext, Quot.sound]`-only discipline, the exclusion SHALL be recorded as an
exclusion — a measured footprint plus a reason — never as a claim of cleanliness.

#### Scenario: A stubbed theorem fails the build

- **WHEN** any theorem in `Codec/` or `Codec.lean` is replaced by `sorry`
- **THEN** the `check` gate fails (non-zero), and the failure names the
  declaration or at least the file, so the gate cannot go green with an
  incomplete proof.

#### Scenario: The documented axiom check runs in-repo

- **WHEN** a reader follows the documentation's "check one law by hand" recipe
- **THEN** the commands reference a `lean-codec` declaration
  (`#print axioms Codec.roundtrip`) and the repository's own toolchain, and they
  succeed from a clean checkout.

#### Scenario: A documented axiom footprint matches the measurement

- **WHEN** a law's docstring or `README.md` states an axiom footprint
- **THEN** that statement matches what `#print axioms` actually reports for it, so a
  law carrying `Classical.choice` is never described as `[propext]`-only, and a law
  excluded from the discipline is described as excluded rather than clean.

#### Scenario: A claim of "proved" names a declaration that exists

- **WHEN** a docstring or a `README.md` section cites a declaration by name as
  authority for a claim (including in a departure/invariant anchor such as `[S3]`)
- **THEN** that name resolves to a real declaration in the same repository, so no
  text asserts a fact "proved as `X`" while `X` was never written and no anchor
  names a symbol that does not exist.

#### Scenario: A guaranteed behaviour names the theorem that guarantees it

- **WHEN** prose states that an input class is rejected, canonical, or otherwise
  guaranteed a property (for example that non-canonical encodings are refused)
- **THEN** that guarantee is stated by a theorem, or is explicitly described as
  unchecked; prose SHALL NOT claim a behaviour is guaranteed when only the
  mechanism that happens to produce it is present and no law pins it.
