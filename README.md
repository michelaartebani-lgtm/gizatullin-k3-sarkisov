# Sarkisov blow-up: a finite lattice check in Magma

This repository contains code supporting the lattice-theoretic computation in the **proof of Proposition 6.11** of:

M. Artebani, A. Garbagnati, and D. Paiva, *Gizatullin's problem for K3 surfaces in Fano threefolds* (manuscript).

## Purpose

Let Y be a Fano threefold with Pic(Y)=ZH_Y, -K_Y=sH_Y and h=H_Y^3. Let S\in|-K_Y| be a smooth K3 surface with Picard number two and set H=H_Y|_S. We work in degree six, so H^2=sh=6.

For a curve C\subset S with arithmetic genus g and degree d=H\cdot C, consider the lattice

\[
L=\langle H,C\rangle,\qquad
\operatorname{Gram}(L)=\begin{pmatrix}6&d\\d&2g-2\end{pmatrix},
\qquad A=sH-C.
\]

The script enumerates **even overlattices** M of L through isotropic subgroups of the discriminant group of L, and screens for numerical conditions necessary if the blow-up of Y along C starts a volume-preserving Sarkisov link **but is not weak Fano** (Proposition 4.17 and the proof of Proposition 6.11).

Specifically, it checks that H is primitive in M; C remains primitive if g=1; \det(M)\notin\{-1,-4\}; and that there exists a class \Gamma satisfying

\[
\Gamma^2=-2,\quad H\cdot\Gamma>0,\quad
2(d-s^2h)<A\cdot\Gamma<0,
\]

such that the residual class after subtracting \Gamma until it has nonnegative pairing with \Gamma still has positive H-degree.

**Important:** passing these tests is a *necessary numerical condition*, not a proof that a suitable irreducible curve exists or that a Sarkisov link exists. The code deliberately does not test every aspect of the very ampleness of \(H\), nor the irreducibility of \Gamma; these can only eliminate candidates. In the manuscript, the remaining candidates are excluded by a separate geometric argument (Proposition 6.12).

## Why the search is finite (an independent numerical check)

Let \Delta=6(2g-2)-d^2<0, and set m=A\cdot\Gamma and n=H\cdot\Gamma. Since C\cdot\Gamma=sn-m and \Gamma\in L^\vee, the equation \Gamma^2=-2 implies

\[
\bigl(6s^2-2sd+2g-2\bigr)n^2
+2m(d-6s)n+6m^2+2\Delta=0.
\]

The range of m is finite: 2(d-6s)<m<0. Writing \mu=\lceil -m/2\rceil, the residual-degree condition gives \mu n<6s-d, so n is also bounded. An exact-arithmetic enumeration of these integer possibilities, checking the induced even overlattice and primitivity conditions, independently reproduces the candidate list in the table below. This provides a useful check on the discriminant-group implementation.

## Files

- `SarkisovBlowup.m`: functions implementing the finite search (does not automatically run the examples).
- `run_examples.m`: calls the search for the three ambient Fano threefolds used in Section 6.

## Running the computation

In a Magma session, from the repository directory:

```magma
load "run_examples.m";
```

Alternatively:

```magma
load "SarkisovBlowup.m";
GoodCases_gd([[2,5]], 2, 3);
```

## Expected candidate pairs

| Threefold | \(s\) | \(h\) | Candidate \((g,d)\) |
|---|---:|---:|---|
| Smooth cubic T in  P^4 | 2 | 3 | (2,5) |
| Smooth quadric Q in P^4 | 3 | 2 | (5,10), (10,11) |
| Smooth (2,3) complete intersection Z in P^5 | 1 | 6 | None |

Representatives of the numerically possible classes, in the basis \((H,C)\), are:

| Threefold, (g,d) | \Gamma | H\cdot\Gamma | A\cdot\Gamma | Residual after stripping |
|---|---|---:|---:|---|
| T, (2,5) | H-C | 1 | -1 | H (subtract once) |
| Q, (5,10) | H-C/2 | 1 | -3 | H (subtract twice) |
| Q, (10,11) | 2H-C | 1 | -1 | H (subtract once) |

In the middle row, \Gamma belongs to a proper even overlattice of index two.

## Reproducibility and scope

- All quadratic-form and discriminant-group operations in the script are exact (integer/rational arithmetic).
- The three examples require sh=6. The function explicitly rejects other values because the Gram matrix has the fixed entry H^2=6.

## Reference in the article

The computational step supports the passage in the proof of Proposition 6.11 that reduces non-weak-Fano candidates to the three pairs above. Proposition 6.12 then excludes the possibility that these cases initiate a Sarkisov link.
 
