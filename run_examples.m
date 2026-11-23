// Reproduce the lattice-theoretic candidates in Proposition 6.11.
// Run in Magma from this directory: load "run_examples.m";
// Expected results (not a claim of geometric realizability):
//  cubic Y=T,  (s,h)=(2,3): [(2,5)]
//  quadric Y=Q, (s,h)=(3,2): [(5,10), (10,11)]
//  (2,3) CI Z, (s,h)=(1,6): []

load "SarkisovBlowup.m";

// Cubic threefold T
s := 2;
h := 3;

List := [
 [g,d] :
 g in [0..s^3*h/2],
 d in [1..s^2*h-1] |
 g lt d^2/(2*s*h)+1
];

GoodCases_gd(List, s, h);

// Quadric threefold Q
s := 3;
h := 2;

List := [
 [g,d] :
 g in [0..s^3*h/2],
 d in [1..s^2*h-1] |
 g lt d^2/(2*s*h)+1
];

GoodCases_gd(List, s, h);

// Complete intersection Z
s := 1;
h := 6;

List := [
 [g,d] :
 g in [0..s^3*h/2],
 d in [1..s^2*h-1] |
 g lt d^2/(2*s*h)+1
];

GoodCases_gd(List, s, h);

