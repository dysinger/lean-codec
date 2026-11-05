# codec/congruence-honesty Specification

## Purpose

Record, as proved facts, which of the library's hypothesis families
(`Unambiguous`, `Functional`, `RelAligned`, `LengthDet`, `LengthConst`, `huniq`)
compose under which `Codec` constructors, and which provably do not — so that a
downstream author is never told a composed codec inherits a leaf's uniqueness when
it does not.

## ADDED Requirements

### Requirement: A predicate's composition status is proved or refuted, never assumed

For each hypothesis family the library exposes, the repository SHALL record whether
that predicate composes under `seq`, `iso`, and `alt`. Each record SHALL be either a
theorem that the composition holds, or a refutation — a theorem exhibiting two
distinct values related to one byte string — with the counterexample stated in
place. A family whose composition status is unknown SHALL NOT be described in prose
or documentation as if it composed.

#### Scenario: A non-congruent family is refuted in place

- **WHEN** a hypothesis family does not compose under a constructor
- **THEN** the repository contains a theorem exhibiting the failure — for the
  recorded `Unambiguous`/`seq` case, two distinct values in the result of decoding
  one one-byte input — and the counterexample is stated where a reader who would
  otherwise assume composition will look.

#### Scenario: A congruent family is proved in place

- **WHEN** a hypothesis family does compose under a constructor
- **THEN** the repository contains a theorem of that implication, so the claim
  rests on a proof rather than on the absence of a counterexample.

### Requirement: A leaf-only supplier is documented as leaf-only

Where a hypothesis family is supplied only for a leaf codec, the repository SHALL
say so at the supplier, and SHALL NOT present leaf satisfiability as evidence that
the family is inherited by composed or downstream codecs. Downstream documentation
SHALL state plainly which guarantees are leaf-only.

#### Scenario: Downstream documentation states the scope of a uniqueness guarantee

- **WHEN** a downstream consumer reads what a uniqueness or functional guarantee
  covers
- **THEN** the documentation states that the guarantee is available at the leaf
  codec and is not inherited by a composed codec, rather than presenting the
  leaf supplier as the general case.

### Requirement: Every hypothesis family with a supplier has one for each mirror

Where the library exposes a pair of mirrored hypothesis families — a left-oriented
and a right-oriented form of the same obligation — both SHALL be supplied, so that
no law rests on a premise that nothing in the repository constructs. A satisfiability
witness added for one member of such a pair SHALL NOT be left without its mirror.

#### Scenario: A fold's termination witness exists for both orientations

- **WHEN** a termination witness is supplied for the left fold's obligation
- **THEN** the right fold's mirrored obligation also has a witness in the
  repository, so the laws of both folds are exercised rather than one being proved
  only under an uninhabited premise.
