// test encrypt / decrypt

test_task1 := true;
test_task2 := true;
test_task3 := true;
test_task4 := true;
test_task5 := true;
test_task6 := true;

sk, pk := BGVKeyGen();
m := RandomMessagePol();
c := BGVEncrypt(m,pk);
mdec := BGVDecrypt(c,sk);
print "Test encrypt / decrypt ", m eq mdec;
print "Noise in fresh ct", BGVNoiseBound(c,sk);

// test mod switch
c1 := BGVModSwitch(c, 1);
print "Noise in switched ct", BGVNoiseBound(c1,sk);
m1 := BGVDecrypt(c1,sk);
print "Test mod switch ", m eq m1;

// test addition 
m1 := RandomMessagePol();
c1 := BGVEncrypt(m1,pk);
m2 := RandomMessagePol();
c2 := BGVEncrypt(m2,pk);
c3 := BGVAdd(c1,c2);
m3 := BGVDecrypt(c3, sk);
print "Test addition ", m3 eq (m1+m2) mod p;
print "Noise in addition", BGVNoiseBound(c3,sk);

// test basic mult 
c3 := BGVBasicMul(c1, c1);
m3 := BGVDecrypt(c3, sk);
print "Test basic multiplication ", m3 eq ((m1*m1) mod f) mod p;
print "Noise in basic mult", BGVNoiseBound(c3,sk);

// generating ksk and testing mult
ksk := BGVKeySwitchingKeyGen(sk^2 mod f, sk);
c3 := BGVMul(c1, c1, ksk);
m3 := BGVDecrypt(c3, sk);
print "Test multiplication with key switch", m3 eq ((m1*m1) mod f) mod p;
print "Noise in mult with key switch", BGVNoiseBound(c3,sk);

if test_task1 then 

print "\n\n\n\n";

// tests for Task 1
ck := c1;
mt := m1;
for k := 2 to 16 do
  ck := BGVBasicMul(ck, c1);
  mk := BGVDecrypt(ck, sk);
  mt := ((mt*m1) mod f) mod p;
  print k;
  print "Test basic multiplication ", mk eq mt;
  print "Noise in basic mult", BGVNoiseBound(ck,sk);
end for;

print "\n\n";

ck := c1;
mt := m1;
for k := 2 to 16 do
  ck := BGVMul(ck, c1, ksk);
  mk := BGVDecrypt(ck, sk);
  mt := ((mt*m1) mod f) mod p;
  print k;
  print "Test multiplication with key switch ", mk eq mt;
  print "Noise in mult with key switch", BGVNoiseBound(ck,sk);
end for;

print "\n\n";

ck := c1;
mt := m1;
for k := 2 to max_level-2 do
  ck := BGVMul(ck, c1, ksk);
  ck := BGVModSwitch(ck,1);
  mk := BGVDecrypt(ck, sk);
  mt := ((mt*m1) mod f) mod p;
  print k;
  print "Test multiplication with mod switch ", mk eq mt;
  print "Noise in mult and mod switch ", BGVNoiseBound(ck,sk);
end for;

print "\n\n";

// test with repeated squaring
ck := c1;
mt := m1;
for k := 1 to max_level-2 do
  ck := BGVMul(ck, ck, ksk);
  ck := BGVModSwitch(ck,1);
  mk := BGVDecrypt(ck, sk);
  print k;
  mt := (mt*mt mod f) mod p;
  print "Test rep squaring mod switch multiplication ", mk eq mt;
  print "Noise in rep squaring mod switch mult", BGVNoiseBound(ck,sk);
end for;

end if;

if test_task2 then 

print "\n\n";

// test Task 2

A := [Random(Fp) : i in [1..N]];
B := [Random(Fp) : i in [1..N]];
a := BGVEncode(A, fs);
b := BGVEncode(B, fs);

asumb := BGVDecode(a+b, fs);
aprodb := BGVDecode((a*b) mod Fpz ! f, fs);

print "Test additive homomorphism ", asumb eq [A[i] + B[i] : i in [1..N]];
print "Test multiplicative homomorphism ", aprodb eq [A[i]*B[i] : i in [1..N]];

end if;

if test_task4 then 

print "\n\n";

// test Task 4

if (toy_set) then 
for k := 1 to 8 do 
   skrec := BGVLatticeAttack(pk, k);
   print "Lattice attack for qb^k with k =", k, skrec eq sk;
end for;
else
   print "Only run lattice attack on toy set";
end if;

end if;

if test_task5 then 

// test Task 5

print "\n\n";

skrec := BGVTrivialKeyRecovery(sk);
print "Trivial key recovery works ", skrec eq sk;
skrec, ncalls := BGVActiveAttack(pk, sk);

print "Active attack works ", sk eq skrec, " using ", ncalls, " calls to decrypt";

end if;

if test_task6 then 

print "\n\n";

qb := GetBaseModulus();
ell := 8;
Zq := Integers(qb^ell);
Zqx<x> := PolynomialRing(Zq);

for k := 2 to 13 do   // mul polys of degree < 2^k

  a := Zqx ! [Random(Zq) : i in [1..2^k]];
  b := Zqx ! [Random(Zq) : i in [1..2^k]];
  
  print "\nMultiplying polys of degree ", 2^k;
  print "School book "; 
  time c1 := SchoolBookMult(a,b);
  print "NTT ";
  omega := PrimitiveNthRoot(ell, 2^(k+1));
  time c2 := FastMult(a, b, omega, 2^(k+1));
  print "Equality ", c1 eq c2;
  
end for;

end if;

