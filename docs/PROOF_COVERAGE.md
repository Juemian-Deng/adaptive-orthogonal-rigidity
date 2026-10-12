# Coverage of checkpoint 033

## Main endpoints

All entries below are actual locally compiled theorems. Independent acceptance
of the complete checkpoint 033 is pending; prior F2/A2 acceptance does not by
itself certify the newly completed F1/A1 chain.

| Result | Source file | Exact Lean endpoint |
| --- | --- | --- |
| F1: `thm:finite` | `FiniteMovementTheorem.lean` | `finite_movement_bound` |
| A1: `thm:main`, both conclusions | `AsymptoticMovementTheorem.lean` | `asymptotic_movement_bound` |
| F2: `thm:block-finite`, both conclusions | `GeometricBlockBound.lean` | `finite_block_bound` |
| A2: `thm:blocks` | `AsymptoticBlockTheorem.lean` | `asymptotic_block_bound` |
| A2 sufficient parameter range | `SufficientBlockRange.lean` | `sufficient_block_range` |

`TargetStatements.lean` contains actual proofs of all five fully quantified
contracts in `AdaptiveOrthogonalRigidity.TargetContracts`.

## Movement proof chain

- Actual compatible-displacement cover: `CompatibleCoverProbability`.
- Original all-boundary Krylov failure probability: `UniformKrylov`; real lift:
  `IntegerColumnLift`, `BoundaryRealKrylov`, `KrylovReindex`.
- Same-target Householder removal, invariant-free capture, localization, and
  ordinary canonical target: `MovementCapture`, `BoundaryLocalization`,
  `LocalizedOrthogonal`, `CanonicalTarget`.
- Rational controlled-subspace descent retaining all needed embedded outputs:
  `RationalControlledSpace`.
- Saturated integral bases, reduction independence, regular descriptor with
  possibly singular leading matrix: `IntegralDescriptorRegular`, using
  `PolynomialPencilKernel`.
- True row-base packing and exact original-edge Fourier estimate:
  `LinearBasePacking`, `PackedActionProbability`, `FiniteDescriptorCount`.
- Original-graph uniform descriptor probability: `UniformDescriptors`.
- Generic joint-output one-step, true original graph-boundary transport,
  and global budgeted termination: `RegularDescriptorReduction`,
  `GraphBoundaryDescriptorStep`, `GlobalBoundaryDescent`.
- Original affine binary-cube event: `UniformAffineCube`.
- Actual original movement-event inclusion in four exceptional events:
  `movementEvent_subset_exceptional`; exact union bound:
  `movement_exceptional_probability`.
- Complete finite assembly: `finite_movement_bound`.
- Explicit rounding, uniform parameter choices, and both probability
  asymptotics: `MovementAsymptoticBounds`, `asymptotic_movement_bound`.

## Bounded-component proof chain

- Actual support components, balance, target-only normalization, and retained
  noncoordinate columns: `SupportComponents`, `PhysicalNormalization`,
  `NoncoordinateComponents`.
- F3 and real modulo-one quadratic atoms and genuine rectangle convolution:
  `F3QuadraticAtom`, `RealQuadraticAtom`, `GramAtoms`.
- Training span, integer-to-real finite projector identification, and fresh
  testing of whole existential left-block events: `TrainingSpan`,
  `FiniteProjectors`, `TrainingTesting`, `GraphTrainingTesting`.
- Orthogonal target rectangle norm constraints: `NecessaryNorms`.
- Actual physical-partition count, deterministic independent splits, finite
  union, and geometric estimate: `PartitionCounting`, `FixedPartitionProbability`,
  `FiniteBlockTheorem`, `GeometricBlockBound`.
- Exact asymptotic constant 1/12 and bounded/oscillating parameter coverage:
  `AsymptoticBlockTheorem`, `SufficientBlockRange`.

## Literal-generality exceptions

These do not weaken any stated F1/F2/A1/A2 endpoint. They do limit a claim that
*every auxiliary manuscript statement at its widest generality* has been
formalized:

1. `lem:fiber`: the implementation proves arbitrary-field affine-fiber bounds
   for the original heterogeneous independent Bernoulli coordinates. The
   manuscript's more general arbitrary-coordinate-distribution version is not
   claimed. Every application in the main graph theorems uses the proved case.
2. `lem:support-lower`: the proved support lower bound applies to the
   minimum-relative-rank matrix selected in the cover proof. The stronger
   standalone assertion for every ternary matrix is not claimed. The exact
   compatible-displacement cover and its constants are proved.
3. `prop:descent`: the implementation proves the general-field one-step
   reduction and the complete original-graph global descent with the bound
   `card(S_final) ≤ card(S_initial) + R*k`. This is the bound needed for F1.
   The manuscript's separately stated general-field global iteration and
   strict `< R*r` budget are not automatically claimed from this interface.
4. `cor:reflections`: the standalone reflection-product corollary is not in
   checkpoint 033. Its underlying movement-rank main theorem is fully proved.

The mathematical model does not assume a witness is rational, fixed before
sampling, independent of the graph, supported on a bounded set, or drawn from a
finite list. Ordinary isomorphism never permits arbitrary sign switches.
Neither asymptotic endpoint assumes its rank/component sequence is monotone
or tends to infinity.
