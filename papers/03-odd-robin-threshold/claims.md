# Claims and evidence — the odd analogue of Robin's 5040

Paths are relative to the repository root.

| # | Claim (precise) | Rigor | Digits | Novelty | Certificate | Lean statement | Witness | Notes |
| --- | --------------- | ----- | ------ | ------- | ----------- | -------------- | ------- | ----- |
| 1 | N = 3⁴·5³·7²·11·13⋯61 = 277093800961598968947975375 violates the odd Robin inequality: V(N) = σ(N)/N − (e^γ/2) log log N = 0.00444312520175774919138456065112827324129… > 0 | numeric-experiment | 60 |  | certificates/03-odd-robin-threshold/odd-robin.json |  |  | σ(N)/N = 24294062139899904/6631081502504681 exactly (`margins.py`). Reproduces Washington–Yang. |
| 2 | c₀ = 67N: V(c₀) = −0.00034342801313684807911297390401553362055… < 0 | numeric-experiment | 60 |  | certificates/03-odd-robin-threshold/odd-robin.json |  |  | Reproduces Washington–Yang. |
| 3 | 3N: V(3N) = −0.00138940196812377892710764024864911778432… < 0, the largest margin among all candidates in (N, c₀) | numeric-experiment | 60 |  | certificates/03-odd-robin-threshold/odd-robin.json |  |  |  |
| 4 | The odd n with N < n < c₀ and σ(n)/n ≥ (e^γ/2) log log(N + 1) form a set of exactly 1098 integers (SHA-256 prefix of the sorted list 4bf6339dd6b9b139), and each has V(n) < 0. Two independent exhaustive enumerations agree | numeric-experiment |  |  | certificates/03-odd-robin-threshold/odd-robin.json |  |  | Methods A (python-flint, Lagrangian pruning) and B (mpmath intervals, elementary pruning); outputs gap.out.txt, checkB.out.txt, candidates\_A.txt = candidates\_B.txt. |
| 5 | No odd n with N < n < c₀ is a violator. Hence RH ⟺ σ(n) < (e^γ/2) n log log n for all odd n > N, and N + 1 is optimal | conjectural |  | answers a question stated by Washington–Yang; no resolution found in the literature |  |  |  | Follows from #1, #4 and Washington–Yang Theorem 1.2. Graded conjectural because the enumeration's completeness is not formalised. |
| 6 | No odd n in (N, 10⁶⁰] is a violator; exactly 884 odd n ≥ 3 below 10¹²⁰ are violators, the largest N. For n coprime to 6 the analogue has 452 604 violators below 10¹²⁰ in the search, the largest in [10¹¹⁹, 10¹²⁰) | numeric-experiment |  |  |  |  |  | scan60.out.txt, coprime\_k1.out.txt, coprime\_k2.out.txt. The k = 0 run (coprime\_k0.out.txt) reproduces the 26 Robin exceptions with n ≥ 3. |
| 7 | For naturals 3 ≤ L ≤ n with n an odd violator, (e^γ/2) log log L ≤ σ(n)/n | proved |  |  |  | lean/SimpleZerosHilbertRobinEpstein/OddRobin/OddRobinCore.lean: violator\_ratio\_ge | three\_violator | Formalises the definition of the candidate set. |
| 8 | For every natural n ≠ 0, σ(n)/n ≤ Π\_{p∣n} p/(p − 1) | proved |  |  |  | lean/SimpleZerosHilbertRobinEpstein/OddRobin/OddRobinCore.lean: sigma\_div\_le\_prod | sigma\_div\_le\_prod\_hyps\_satisfiable | The pruning inequality of method B. |

## Reasoning

### #1 to #3

σ(n)/n is the exact rational Π (q^(e+1) − 1)/(q^e (q − 1)). `margins.py` subtracts (e^γ/2) log log n twice: in mpmath at 120 significant digits, and in python-flint balls at 400 bits. Both agree in every printed digit, and the balls decide the sign rigorously.

### #4

Every violator n ≥ N + 1 has σ(n)/n ≥ f(N + 1), since f is increasing. So the violators in the gap lie among these candidates.

- **Method A** enumerates them by depth-first search with the Lagrangian bound of main.md §2.
- **Method B** uses an unrelated elementary bound (at most m distinct primes, each factor at most q/(q − 1)), a different traversal, and mpmath interval arithmetic.

Both return the same 1098 integers, and all margins are negative. A shared error would have to sit in the one-line definition of the candidate set, which is formalised in #7. An error in both pruning implementations is unlikely, because the two bounds are unrelated.

### #5

From #1 and #4, N is the largest odd violator below c₀. If RH holds, Washington–Yang give the inequality for n ≥ c₀, and #4 gives it for N < n < c₀. Conversely, the inequality for all n > N includes all n ≥ c₀, which gives RH. N + 1 is optimal because N violates.

### #7, #8

These are kernel-checked theorems; their axioms are listed by `lean/AxiomCheck.lean`.
- **#7:** log log is increasing on [3, ∞), so the monotonicity follows.
- **#8:** by multiplicativity of σ, and σ(p^e)(p − 1) = p^(e+1) − 1 < p · p^e for each prime power.
