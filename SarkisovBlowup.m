///////////////////////////////////////////////////////////////////////////
// Gizatullin's problem for degree-six K3 surfaces in Fano threefolds
// Computational check used in the proof of Proposition 6.11.
//
// L = <H,C>, Gram(L) = [[6,d],[d,2g-2]], H^2 = s*h = 6.
// A = s*H - C.  The three applications have
//   (s,h) = (2,3) [cubic], (3,2) [quadric], (1,6) [(2,3) CI].
//
// This script enumerates even overlattices M of L and searches for
// NUMERICAL CANDIDATES for a non-nef anticanonical class A.
// The following are necessary, not sufficient, geometric conditions:
//  1. H remains primitive in M;
//  2. if g=1, C remains primitive in M;
//  3. det(M) is neither -1 nor -4;
//  4. there exists Gamma in M with Gamma^2=-2 and H.Gamma>0,
//                2*(d-s^2*h) < A.Gamma < 0;
//  5. after repeatedly subtracting Gamma from A until its intersection
//     with Gamma is nonnegative, the residual D has D.H>0.
//
// No separate test of very ampleness of H is imposed here: such a
// test would only remove candidates. The geometric proof assumes H
// very ample and excludes the remaining possibilities separately.
// In particular, an effective class of square -2 is NOT assumed to
// be an irreducible (-2)-curve or to be non-big.
////////////////////////////////////////////////////////////////////////////

Z := Integers();
Q := Rationals();

RootRec := recformat<
 coords,
 original_coords,
 H_degree,
 A_dot,
 residual_coords,
 residual_original_coords,
 residual_H_degree,
 residual_Gamma_dot,
 removed_multiplicity
>;

OverRec := recformat<
 subgroup_order,
 basis,
 gram,
 Hcoords,
 Fcoords,
 Acoords,
 A_lower_bound,
 roots
>;

///////////////////////////////////////////////////////////////////////////
// Auxiliary functions
///////////////////////////////////////////////////////////////////////////

DotLat := function(u, G, v)
 return &+[ u[i]*G[i,j]*v[j] : i in [1..2], j in [1..2] ];
end function;

SquareLat := function(u, G)
 return DotLat(u, G, u);
end function;

IsEvenInteger := function(x)
 return Denominator(x) eq 1 and (Z!Numerator(x)) mod 2 eq 0;
end function;

IsDivisibleInteger := function(a, b)
 if b eq 0 then
 error "Division by zero.";
 end if;
 return a mod Abs(b) eq 0;
end function;

///////////////////////////////////////////////////////////////////////////
// Discriminant group and isotropic subgroups
///////////////////////////////////////////////////////////////////////////

PreimageVector := function(x, pi)
 AL := Codomain(pi);
 xx := AL!x;
 y := xx @@ pi;
 return [ Z!c : c in Eltseq(y) ];
end function;

DiscriminantQuadraticValue := function(x, pi, Ginv)
 z := Vector(Q, PreimageVector(x, pi));
 return &+[ z[i]*Ginv[i,j]*z[j] : i in [1..2], j in [1..2] ];
end function;

IsIsotropicElement := function(x, pi, Ginv)
 qx := DiscriminantQuadraticValue(x, pi, Ginv);
 return IsEvenInteger(qx);
end function;

IsIsotropicSubgroup := function(K, pi, Ginv)
 for x in K do
 if not IsIsotropicElement(x, pi, Ginv) then
 return false;
 end if;
 end for;
 return true;
end function;

///////////////////////////////////////////////////////////////////////////
// Construction of the overlattice associated with an isotropic subgroup
///////////////////////////////////////////////////////////////////////////

OverlatticeBasis := function(K, pi, G)
 GQ := ChangeRing(G, Q);
 Ginv := GQ^(-1);
 gens := [Vector(Q, [1,0]),Vector(Q, [0,1])];
 // We add the lifts in L^vee of the generators of the isotropic subgroup K.
 for x in Generators(K) do
 z := Vector(Q, PreimageVector(x, pi));
 v := z*Ginv;
 Append(~gens, v);
end for;

 // We clear denominators.
 D := 1;
 for v in gens do
 for c in Eltseq(v) do
 D := LCM(D, Denominator(c));
 end for;
 end for;

 rows := [];

 for v in gens do
 Append(~rows, [ Z!(D*c) : c in Eltseq(v) ]);
 end for;

 M := Matrix(Z, rows);
 HNF := HermiteForm(M);
 basisRows := [];

 for i in [1..Nrows(HNF)] do
 row := [ HNF[i,j] : j in [1..2] ];
 if row ne [0,0] then
 Append(~basisRows, row);
 end if;
 end for;

 if #basisRows ne 2 then
 error "Error in the construction of the overlattice basis.";
 end if;

 B := ChangeRing(Matrix(Z, basisRows), Q) * (1/D);
 return B;

end function;

///////////////////////////////////////////////////////////////////////////
// Coordinates and primitivity of a vector in the overlattice
///////////////////////////////////////////////////////////////////////////

CoordinatesInBasis := function(v, B)
 vv := Vector(Q, v);
 coords := vv*B^(-1);
 if &or[ Denominator(c) ne 1 : c in Eltseq(coords) ] then
 return false, [];
 end if;
 return true, [ Z!c : c in Eltseq(coords) ];
end function;

IsPrimitiveInOverlattice := function(v, B)
 ok, coords := CoordinatesInBasis(v, B);
 if not ok then
 return false, [];
 end if;
 return GCD([ Abs(c) : c in coords ]) eq 1, coords;
end function;

///////////////////////////////////////////////////////////////////////////
// Subtracts Gamma from A as long as the intersection with Gamma is negative
///////////////////////////////////////////////////////////////////////////

StripGammaFromA := function(GM, Hcoords, Acoords, Gammacoords)
 Dcoords := Acoords;
 mult := 0;
 while DotLat(Dcoords, GM, Gammacoords) lt 0 do
 Dcoords := [ Dcoords[i] - Gammacoords[i] : i in [1..2] ];
 mult +:= 1;
 end while;

 DH := DotLat(Hcoords, GM, Dcoords);
 DGamma := DotLat(Dcoords, GM, Gammacoords);

 return DH gt 0, Dcoords, DH, DGamma, mult;
end function;

///////////////////////////////////////////////////////////////////////////
// Finite search for roots using the bound on A.Gamma
///////////////////////////////////////////////////////////////////////////

FindRootsWithADotBound := function(GM, B, Hcoords, Acoords, ALower)

 roots := [];

 // We search for Gamma with:
 //
 // Gamma^2 = -2,
 // H.Gamma > 0,
 // ALower < A.Gamma < 0.
 //
 // Moreover, setting D=A and subtracting Gamma as long as D.Gamma<0,
 // we require that the residual class D satisfies D.H>0.

 if ALower ge -1 then
 return roots;
 end if;

 // Pairing with A in the basis of the overlattice:
 //
 // A.(x e1 + y e2) = l1*x + l2*y.

 l1 := DotLat(Acoords, GM, [1,0]);
 l2 := DotLat(Acoords, GM, [0,1]);

 g0, u, v := XGCD(l1, l2);

 if g0 lt 0 then
 g0 := -g0;
 u := -u;
 v := -v;
 end if;

 if g0 eq 0 then
 // A would have zero pairing with the whole lattice.
 // Then there cannot exist Gamma with A.Gamma<0.
 return roots;
 end if;

 for m in [ALower + 1 .. -1] do

 if m mod g0 ne 0 then
 continue;
 end if;

 mult := m div g0;

 // A particular solution of l1*x + l2*y = m.
 x0 := u * mult;
 y0 := v * mult;

 // Generator of the kernel of l1*x + l2*y.
 kx := l2 div g0;
 ky := -l1 div g0;

 // All solutions are:
 //
 // Gamma(t) = (x0,y0) + t*(kx,ky).
 //
 // We now impose Gamma(t)^2 = -2.

 aa := SquareLat([kx,ky], GM);
 bb := 2 * DotLat([x0,y0], GM, [kx,ky]);
 cc := SquareLat([x0,y0], GM) + 2;

 possible_t := { Z | };

 if aa eq 0 then

 if bb ne 0 and IsDivisibleInteger(-cc, bb) then
 Include(~possible_t, (-cc) div bb);
 end if;

 else

 disc := bb^2 - 4*aa*cc;

 if disc ge 0 then

 is_sq, sdisc := IsSquare(disc);

 if is_sq then

 den := 2*aa;

 num1 := -bb + sdisc;
 num2 := -bb - sdisc;

 if IsDivisibleInteger(num1, den) then
 Include(~possible_t, num1 div den);
 end if;

 if IsDivisibleInteger(num2, den) then
 Include(~possible_t, num2 div den);
 end if;

 end if;

 end if;

 end if;

 for t in possible_t do

 Gamma := [ x0 + t*kx, y0 + t*ky ];

 Gamma2 := SquareLat(Gamma, GM);
 HGamma := DotLat(Hcoords, GM, Gamma);
 AGamma := DotLat(Acoords, GM, Gamma);

 if Gamma2 eq -2 and HGamma gt 0 and AGamma gt ALower and AGamma lt 0 then

 okResidual, Dcoords, DH, DGamma, stripMult :=
 StripGammaFromA(GM, Hcoords, Acoords, Gamma);

 if okResidual then

 GammaOrig := Vector(Q, Gamma) * B;
 Dorig := Vector(Q, Dcoords) * B;

 Append(~roots, rec< RootRec |
 coords := Gamma,
 original_coords := Eltseq(GammaOrig),
 H_degree := HGamma,
 A_dot := AGamma,
 residual_coords := Dcoords,
 residual_original_coords := Eltseq(Dorig),
 residual_H_degree := DH,
 residual_Gamma_dot := DGamma,
 removed_multiplicity := stripMult
 >);

 end if;

 end if;

 end for;

 end for;

 return roots;

end function;

///////////////////////////////////////////////////////////////////////////
// Main function for a pair (g,d), also given s and h
///////////////////////////////////////////////////////////////////////////

CheckPair_gd := function(g, d, s, h)

 if g lt 0 then
 printf "Need g >= 0.\n";
 return [];
 end if;

 if d lt 1 then
 printf "Need d >= 1.\n";
 return [];
 end if;

 if s le 0 then
 printf "Need s > 0.\n";
 return [];
 end if;

 if h le 0 then
 printf "Need h > 0.\n";
 return [];
 end if;

 if s*h ne 6 then
 error "This implementation assumes H^2 = s*h = 6.";
 end if;

 G := Matrix(Z, 2, 2, [6, d, d, 2*g - 2]);

 detG := Determinant(G);

 H := [1,0];
 Fclass := [0,1];
 A := [s,-1];

 H2 := DotLat(H, G, H);
 AH := DotLat(A, G, H);
 A2 := SquareLat(A, G);

 ALower := 2*(d - s^2*h);

 printf "========================================\n";
 printf "Case (g,d) = (%o,%o), s=%o, h=%o\n", g, d, s, h;
 printf "Gram matrix L:\n%o\n", G;
 printf "det(L) = %o\n", detG;
 printf "H^2 = %o\n", H2;
 printf "A = [%o,-1]\n", s;
 printf "A.H = %o\n", AH;
 printf "A^2 = %o\n", A2;
 printf "Lower bound for A.Gamma: A.Gamma > %o\n", ALower;

 if g eq 1 then
 printf "Since g=1, the class F=[0,1] has F^2=0 and will be required to be primitive.\n";
 end if;

 ///////////////////////////////////////////////////////////////////////////
 // Initial necessary conditions
 ///////////////////////////////////////////////////////////////////////////

 
 if detG ge 0 then
 printf "The lattice is not hyperbolic of signature (1,1).\n";
 return [];
 end if;
 if ALower ge -1 then
 printf "There are no integers A.Gamma with %o < A.Gamma < 0.\n", ALower;
 return [];
 end if;

 GQ := ChangeRing(G, Q);
 Ginv := GQ^(-1);

 //////////////////////////////////////////////////////////////////////////////////////////////////////
 // Construction of A_L = Z^2 / GZ^2 and the isotropic subgroups.
 ///////////////////////////////////////////////////////////////////////////////////////////////////////

 FreeG := FreeAbelianGroup(2);

 // The relations are given by the columns of the Gram matrix.
 rel1 := FreeG![ G[1,1], G[2,1] ];
 rel2 := FreeG![ G[1,2], G[2,2] ];

 AL, pi := quo< FreeG | [rel1, rel2] >;

 printf "#A_L = %o\n", #AL;

 allSubs := [ S`subgroup : S in Subgroups(AL) ];

 isoSubs := [];

 for K in allSubs do

 if IsIsotropicSubgroup(K, pi, Ginv) then
 Append(~isoSubs, K);
 end if;

 end for;

 printf "Number of isotropic subgroups = %o\n", #isoSubs;

 good := [];

 ///////////////////////////////////////////////////////////////////////////
 // Analysis of the overlattices.
 ///////////////////////////////////////////////////////////////////////////

 for K in isoSubs do

 B := OverlatticeBasis(K, pi, G);

 GMQ := B * GQ * Transpose(B);

 // Check that the matrix is integral.
 if &or[ Denominator(GMQ[i,j]) ne 1 : i in [1..2], j in [1..2] ] then
 continue;
 end if;

 GM := Matrix(Z, 2, 2, [ Z!GMQ[i,j] : i in [1..2], j in [1..2] ]);

 // Check that the overlattice is even.
 if &or[ GM[i,i] mod 2 ne 0 : i in [1..2] ] then
 continue;
 end if;

 // The rank-two even lattices of determinant -1 or -4 admit no
 // very ample polarization of square 6 (see Proposition 6.3).
 // They are excluded on geometric grounds.
 if Determinant(GM) in {-1,-4} then
 continue;
 end if;

 // H must remain primitive.
 primH, Hcoords := IsPrimitiveInOverlattice(H, B);

 if not primH then
 continue;
 end if;

 // We do not test very ampleness of H here (a deliberate relaxation).

 // If g=1, then F=[0,1] has square zero and must remain primitive.
 Fcoords := [];

 if g eq 1 then

 primF, FcoordsTest := IsPrimitiveInOverlattice(Fclass, B);

 if not primF then
 continue;
 end if;

 Fcoords := FcoordsTest;

 end if;

 okA, Acoords := CoordinatesInBasis(A, B);

 if not okA then
 printf "Warning: A does not belong to the overlattice. Skipping this case.\n";
 continue;
 end if;

 roots := FindRootsWithADotBound(GM, B, Hcoords, Acoords, ALower);

 if #roots gt 0 then

 Append(~good, rec< OverRec |
 subgroup_order := #K,
 basis := B,
 gram := GM,
 Hcoords := Hcoords,
 Fcoords := Fcoords,
 Acoords := Acoords,
 A_lower_bound := ALower,
 roots := roots
 >);

 end if;

 end for;

 ///////////////////////////////////////////////////////////////////////////
 // Print result.
 ///////////////////////////////////////////////////////////////////////////

 printf "\nNumber of candidate overlattices = %o\n", #good;

 if #good eq 0 then
 printf "No overlattice satisfies the numerical necessary conditions.\n";
 return [];
 end if;

 printf "Numerical candidates found (not geometric realizations).\n";

 for i in [1..#good] do

 printf "\n----------------------------------------\n";
 printf "Overlattice %o\n", i;
 printf "Index [M:L] = %o\n", good[i]`subgroup_order;
 printf "Basis of M in the coordinates of the basis of L:\n%o\n", good[i]`basis;
 printf "Gram matrix of M:\n%o\n", good[i]`gram;
 printf "det(M) = %o\n", Determinant(good[i]`gram);
 printf "Coordinates of H in M: %o\n", good[i]`Hcoords;

 if g eq 1 then
 printf "Coordinates of F=[0,1] in M: %o\n", good[i]`Fcoords;
 end if;

 printf "Coordinates of A=[%o,-1] in M: %o\n", s, good[i]`Acoords;
 printf "Interval used: %o < A.Gamma < 0\n", good[i]`A_lower_bound;
 printf "Roots found: %o\n", #good[i]`roots;

 for j in [1..#good[i]`roots] do

 Gamma := good[i]`roots[j];

 printf " Gamma %o:\n", j;
 printf " Gamma in the basis of M = %o\n", Gamma`coords;
 printf " Gamma in the original coordinates of L = %o\n",
 Gamma`original_coords;
 printf " H.Gamma = %o\n", Gamma`H_degree;
 printf " A.Gamma = %o\n", Gamma`A_dot;
 printf " I subtract Gamma %o times from A.\n",
 Gamma`removed_multiplicity;
 printf " Residual D in the basis of M = %o\n",
 Gamma`residual_coords;
 printf " Residual D in the original coordinates of L = %o\n",
 Gamma`residual_original_coords;
 printf " D.H = %o\n", Gamma`residual_H_degree;
 printf " D.Gamma = %o\n", Gamma`residual_Gamma_dot;

 end for;

 end for;

 return good;

end function;

///////////////////////////////////////////////////////////////////////////
// Function for a list of pairs
///////////////////////////////////////////////////////////////////////////

CheckList_gd := function(ListGD, s, h)

 // I use a Magma list [* *], not a sequence [].
 // This avoids coercion errors when good contains records.
 results := [* *];

 for gd in ListGD do

 g := gd[1];
 d := gd[2];

 printf "\n\n########################################\n";
 printf "Checking the pair (g,d) = (%o,%o)\n", g, d;
 printf "########################################\n";

 good := CheckPair_gd(g, d, s, h);

 Append(~results, <g,d,good>);

 end for;

 return results;

end function;

///////////////////////////////////////////////////////////////////////////
// Extracts from results only the pairs that are good
///////////////////////////////////////////////////////////////////////////

GoodCasesFromResults_gd := function(results)

 goodCases := [* *];

 for r in results do

 g := r[1];
 d := r[2];
 good := r[3];

 if #good gt 0 then
 Append(~goodCases, <g,d>);
 end if;

 end for;

 printf "\n========================================\n";
 printf "Candidate pairs passing the necessary conditions:\n";
 printf "========================================\n";

 if #goodCases eq 0 then
 printf "No numerical candidates found.\n";
 else
 for gd in goodCases do
 printf "(g,d) = (%o,%o)\n", gd[1], gd[2];
 end for;
 end if;

 return goodCases;

end function;

///////////////////////////////////////////////////////////////////////////
// Single command: checks a list and returns only the good cases
///////////////////////////////////////////////////////////////////////////

GoodCases_gd := function(ListGD, s, h)

 results := CheckList_gd(ListGD, s, h);

 return GoodCasesFromResults_gd(results);

end function;
