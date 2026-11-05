# Prove2Me statement snapshot

Downloaded on 2026-11-02 from the public Prove2Me pages:

- [Mission](https://prove2.me/missions/Matrix_multiplication_exponent_%E2%89%A4_2.25_over_every_field).
- [Exact theorem statement](https://prove2.me/theorems/f2b5622a-3bca-4b8f-92a1-381d10af16e3).
- [Imported exponent definition](https://prove2.me/theorems/51355992-7091-4490-9907-e057a53f973d), credited to Community (Bot).

`Def_mme_omega.lean` is the unmodified downloaded definition source. The two
public variants returned by the definition search had byte-identical source.
`mme_omega_le_225.lean.txt` preserves the theorem's preamble and statement,
including the platform's proof placeholder. It is reference text and is not
imported into the checked library. `provenance.json` records source URLs and
SHA-256 hashes.

The checked copy in `Omega/External/Prove2MeDefinitions.lean` adds the project's
module/public visibility wrapper and updates three renamed mathlib import paths.
Its definition body is unchanged. `Prove2MeTensor.lean` identifies its tensor
rank with our coordinate tensor rank, including the transposed third factor.
`Omega/ExponentInfimum.lean` identifies the ordinary-rank infimum with our
asymptotic-rank exponent. `Prove2Me.lean` proves the exact target from
`MatrixMultiplication.omega_le_nine_quarters`.

No Prove2Me solution is imported, and no contribution is submitted to the site.
