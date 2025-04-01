//Dheeraj Kumar Suryakari, r1032106
// Used chatGPT and Claude ai for understanding crashes and debugging
//https://github.com/dhamarkeshwar/Project_1

clear;

// system parameters 

toy_set := true;  // set this to false for standard parameter set

Z := Integers();
Zx<x> := PolynomialRing(Z);

N := 2^6;
if (not toy_set) then N := 2^10; end if;
f := x^N+1;  // polynomial modulus

p := 2^16+1;  // plaintext modulus 
Fp := GF(p);
Fpz<z> := PolynomialRing(Fp);
facs := Factorisation(Fpz ! f);
fs := [facs[i][1] : i in [1..#facs]];  // factors of f(x) for use in encoding / decoding
alpha := -Coefficient(fs[1], 0);

qb := 7*2^15*p + 1;  // base q for the ciphertext modulus, chosen = 1 mod p and coprime by construction

max_level := 8;  // max number of levels
if (not toy_set) then max_level := 12; end if;

dq := qb^max_level;  // default ciphertext modulus 
B := 5;  // errors are uniformly sampled from [-B,B]

// quick method to get max ciphertext modulus
function GetMaxModulus()
    return dq;
end function;

// quick method to get base ciphertext modulus
function GetBaseModulus()
    return qb;
end function;

// quick method to get plaintext modulus
function GetPlaintextMod()
  return p;
end function;

// quick method to get max level of ciphertext
function GetMaxLevel()
    return max_level;
end function;

// quick method to get max level of ciphertext
function GetDimension()
	return N;
end function;

// sample error polynomial
function ErrorPol()
    return Zx![Z | Random(-B,B): i in [1..N]];
end function;

// sample random polynomial with coefficients in [0..bound-1]
function RandPol(bound)
    return Zx![Z | Random(bound-1) : i in [1..N]];
end function;

// sample ternary polynomial 
function TernaryPol()
   return Zx![Z | Random(-1,1): i in [1..N]];
end function;

function RandomMessagePol()
  return Zx ! [Random(p-1) : i in [1..N]];
end function;

// centered reduction of a mod qi
function CenterRed(a, qi)

  res := a mod qi;
  if (res gt qi/2) then
    res -:= qi;
  end if;

  return res;

end function;

// centered reduction of g mod qi
function CenterRedPol(g, qi)

  return Zx ! [CenterRed(ci, qi) : ci in Eltseq(g)];

end function;

// infinity norm of polynomial with coefficients over Z
function InfNorm(a) 
  return Maximum([AbsoluteValue(ai) : ai in Eltseq(a)]);
end function;

// BGV key generation
function BGVKeyGen()

 q := GetMaxModulus();
 a := RandPol(q);
 e := ErrorPol();
 s := TernaryPol();

 return s, [((a*s + p*e) mod f) mod q, -a mod q];
 
end function;


// key switching key of sk2 under sk1
function BGVKeySwitchingKeyGen(sk2, sk1)

 q := GetMaxModulus();
 qb := GetBaseModulus();
 ksk := [];
 for i := 0 to GetMaxLevel()-1 do
   a := RandPol(q);
   e := ErrorPol();
   Append(~ksk, [((a*sk1 + p*e + qb^i*sk2) mod f) mod q, -a mod q]);
 end for;

 return ksk;
 
end function;

// ciphertext is tuple with first entry actual ciphertext coefficients and second entry level of ciphertext
function BGVEncrypt(m, pk)   

 q := GetMaxModulus();
 u := TernaryPol();
 return <[ ((u*pk[1] + p*ErrorPol() + m) mod f) mod q, ((u*pk[2] + p*ErrorPol()) mod f) mod q ], GetMaxLevel()>;

end function;


// computes partial decryption of ciphertext ct under sk
function BGVPartialDecrypt(ct, sk)

level := ct[2];
 qell := GetBaseModulus()^level;
 coeffs := ct[1];
 part_dec := coeffs[1];
 si := sk;
 for i := 2 to #coeffs do
   part_dec := ((part_dec + coeffs[i]*si) mod f) mod qell;
   if (i lt #coeffs) then 
     si := (si*sk) mod f;
   end if;
 end for;

 return CenterRedPol(part_dec, qell);
end function;

// decryption is just partial decryption mod p
function BGVDecrypt(ct, sk)   
 return BGVPartialDecrypt(ct, sk) mod p; 
end function;

// bound on size of partial decrypt, if this gets close to q/2 expect decryption failure
function BGVNoiseBound(c, sk)
  norm := InfNorm(BGVPartialDecrypt(c, sk));
  if norm eq 0 then
    return -1;
  else
    return Log(2, norm);
  end if;
end function;

// modulus switch over qb^t if there is enough room
function BGVModSwitch(ct, t)
  ell := ct[2];
  coeffs := ct[1];
  if (t ge ell) or (t lt 1) then error "Number of levels higher than available"; end if; 
  
  qb := GetBaseModulus();
  rell := ell - t;
  
  // need to divide everything by qb^t, first need to make everything divisible
  
  _, invp, _ := XGCD(p,qb^t);  // inverse of p mod qb^t  
  coeffsd := coeffs;
  
  for i := 1 to #coeffsd do
    delta := p*CenterRedPol(-coeffs[i]*invp mod qb^t, qb^t);
	coeffsd[i] +:= delta;
	coeffsd[i] := (coeffsd[i] div qb^t) mod qb^rell;
  end for;
  
  return <coeffsd, rell>;

end function;

// TASK 1

function BGVAdd(c_1,c_2)
  if (c_1[2] le c_2[2]) then 
    level := c_1[2];
  else 
    level := c_2[2];
  end if;
  qb := GetBaseModulus()^level;
  cc := <[((c_1[1][1]+c_2[1][1])mod f)mod qb,((c_1[1][2]+c_2[1][2])mod f)mod qb],level>;
  return cc;// think about mod f
end function;

function BGVBasicMul(c_1,c_2)
  if (c_1[2] le c_2[2]) then 
    level := c_1[2];
  else 
    level := c_2[2];
  end if;
  q := GetBaseModulus()^level;
  cc := <[((c_1[1][1]*c_2[1][1])mod f)mod q,((c_1[1][1]*c_2[1][2]+c_1[1][2]*c_2[1][1])mod f)mod q,((c_1[1][2] * c_2[1][2])mod f)mod q],level>;
  return cc;
end function;

function BGVKeySwitch(g,ell,ksk) // outputs a list of ciphers of q_b*s^2 multiplied by pieces of g
  cs := [];
  max_mod := GetMaxModulus();
  temp := g mod qb;
  upd_1 := (ksk[1][1]*temp) mod f;
  upd_2 := (ksk[1][2]*temp) mod f;
  for i := 2 to max_level do
    temp := g-temp; // think about this once
    temp := (temp mod qb^i) div qb^(i-1);
    upd_1 := upd_1+(ksk[i][1]*temp) mod f;
    upd_2 := upd_2+(ksk[i][2]*temp) mod f;
  end for;
  return <[upd_1,upd_2],max_level>;
end function;

function BGVMul(c_1,c_2,ksk)
  cs := BGVBasicMul(c_1,c_2); // Gives 3 component cipher
  result := <[cs[1][1],cs[1][2]],cs[2]>; // First 2 cipher components
  cs_1 := BGVKeySwitch(cs[1][3],cs[2],ksk); 
  return BGVAdd(result,cs_1);
end function;

// last question in task 1 incomplete

// Task 2

function BGVEncode(m,fs)
  // encoded_m := 0;
  // for i :=1 to #fs do
  //   field := quo<Fpz ! Ideal(fs[i])>;
  //   temp := f div fs[i];
  //   inv_temp := ReciprocalPolynomial(temp);
  //   encoded_m := encoded_m + m[i]*temp*inv_temp;
  // end for;
  // return encoded_m;
  m_polys := [Polynomial([m[i]]) : i in [1..#m]]; // Representing finite field elements as elements of zero degree in a polynomial ring - This line from chatgpt
  return CRT(m_polys,fs);
end function;

function BGVDecode(m,fs)
  decoded := [];
  for i := 1 to #fs do
    Append(~decoded, Modexp(m,1,fs[i]));
  end for;
  return decoded;
end function;

// Task 4

function BGVLatticeAttack(pk, ell)
  vec_pk_1 := Coefficients(pk[1]);
  vec_pk_1 := [vec_pk_1[i] mod qb^ell : i in [1..N]];
  vec_pk_1 := [Z | vec_pk_1[i] : i in [1..N]];
  vec_pk_2 := Coefficients(pk[2]);
  vec_pk_2 := [vec_pk_2[i] mod qb^ell : i in [1..N]];
  vec_pk_2 := [Z | vec_pk_2[i] : i in [1..N]];
  M := DiagonalMatrix(Z, N+2, [1 : i in [1..N+2]]);
  zero_column := ZeroMatrix(Z, N+2, 1);
  M_1 := HorizontalJoin(M, zero_column);
  A_n_1 := [vec_pk_2[i] : i in [2..N]];
  Rev_A_n_1 := Reverse(Eltseq(A_n_1));
  A := Vector([-vec_pk_2[1]] cat Eltseq(Rev_A_n_1) cat [p, -vec_pk_1[1], qb^ell]);
  Modified_M := VerticalJoin(M_1, A);
  L := Lattice(Transpose(Modified_M));
  short_vec := BKZ(L,20);
  short_vec_1 := Basis(short_vec)[1];
  short_vec_2 := Vector(Eltseq(short_vec_1));
  poly_sec := &+[Zx!short_vec_2[i]*x^(i-1) : i in [1..N]];
  //print "-poly_sec", -poly_sec;
  if BGVDecrypt(<pk, ell>, poly_sec) eq 0 then
    return poly_sec;
  elif BGVDecrypt(<pk, ell>, -poly_sec) eq 0 then
    return -poly_sec;
  else
    return 0;
  end if;
end function;

// Task 5

function BGVTrivialKeyRecovery(sk)
  temp := BGVDecrypt(<[0,1],max_level>,sk); //gets secret key in mod p
  for i := 0 to N-1 do // -1 is mapped to p-1, so replacing p-1 coefficients with -1
    if Coefficient(temp,i) eq p-1 then // Coefficient function got to know of it from Chatgpt
     temp := temp+(-1-p+1)*x^i;
    end if;
  end for;
  return temp;
end function;

function BGVActiveAttack(pk, sk)
  pk_1 := <pk, max_level>;
  pos_temp_coeff := [];
  neg_temp_coeff := [];
  decrypt_calls := 0;
  for i := 1 to N do
    pk_1[1][1] := pk_1[1][1] + Floor(dq/2)*x^(i-1);
    success := 0;
    temp := p*x^(i-1);
    err := 1;
    decrypt_calls := decrypt_calls + 1;
    if BGVDecrypt(pk_1, sk) eq 0 then Append(~pos_temp_coeff, 0);
    else
      while (success eq 0) and (BGVDecrypt(pk_1, sk) ne 0) do
        if BGVDecrypt(<[pk_1[1][1] - temp, pk_1[1][2]], max_level>, sk) eq 0 then
          pk_1[1][1] := pk_1[1][1] - temp;
          Append(~pos_temp_coeff, -err);
          success := 1;
        elif BGVDecrypt(<[pk_1[1][1] + temp, pk_1[1][2]], max_level>, sk) eq 0 then
          pk_1[1][1] := pk_1[1][1] + temp;
          Append(~pos_temp_coeff, err);
          success := 1;
        end if;
        decrypt_calls := decrypt_calls + 3;
        temp := temp + p*x^(i-1);
        err := err + 1;
      end while;
    end if;
  end for;
  pos_poly_err := &+[Zx!pos_temp_coeff[i]*x^(i-1) : i in [1..N]];
  pk_2 := <pk, max_level>;
  for i := 1 to N do
    pk_2[1][1] := pk_2[1][1] - Floor(dq/2)*x^(i-1);
    success := 0;
    temp := p*x^(i-1);
    err := 1;
    if BGVDecrypt(pk_2, sk) eq 0 then Append(~neg_temp_coeff, 0);
    else
      while (success eq 0) and (BGVDecrypt(pk_2, sk) ne 0) do
        if BGVDecrypt(<[pk_2[1][1] - temp, pk_2[1][2]], max_level>, sk) eq 0 then
          pk_2[1][1] := pk_2[1][1] - temp;
          Append(~neg_temp_coeff, -err);
          success := 1;
        elif BGVDecrypt(<[pk_2[1][1] + temp, pk_2[1][2]], max_level>, sk) eq 0 then
          pk_2[1][1] := pk_2[1][1] + temp;
          Append(~neg_temp_coeff, err);
          success := 1;
        end if;
        decrypt_calls := decrypt_calls + 3;
        temp := temp + p*x^(i-1);
        err := err + 1;
      end while;
    end if;
    decrypt_calls := decrypt_calls + 1;
  end for;
  neg_poly_err := &+[Zx!neg_temp_coeff[i]*x^(i-1) : i in [1..N]];
  dq_negator := Zx![Z | Floor(dq/2) : i in [1..N]];
  // -(pos_poly_err + neg_poly_err) = e
  e := -(pos_poly_err + neg_poly_err);// error polynomial
  as := (pk[1]-p*e) mod dq;
  // print "error poly", e;
  coeffs_as := Coefficients(as);
  coeffs_a := Coefficients(-pk[2]);
  circulantMatrix := Matrix(Integers(dq), N, N, [[coeffs_a[(i-j) mod N + 1] * (1 - 2*((i-j lt 0) select 1 else 0)) : j in [1..N]] : i in [1..N]]);
  vec_coeffs_as := Vector(Integers(dq), coeffs_as);
  vec_s := Solution(Transpose(circulantMatrix), vec_coeffs_as);
  cor_vec_s := [Z | vec_s[i] eq (dq-1) select -1 else vec_s[i] : i in [1..N]];
  poly_sec := &+[Zx!cor_vec_s[i]*x^(i-1) : i in [1..N]];
  if BGVDecrypt(<pk,max_level>, poly_sec) eq 0 then
    return poly_sec, decrypt_calls;
  else
    return "wrong";
  end if;
end function;



// Task 6

qb := GetBaseModulus();
ell := 8;
Zq := Integers(qb^ell);
Zqx<x> := PolynomialRing(Zq);

function RecNTT(a, w, N)
  if N eq 1 then 
    return [a[1]];
  else;
    even_part := [Zq | a[i] : i in [1..#a] | (i mod 2) eq 1];
    odd_part := [Zq | a[i] : i in [1..#a] | (i mod 2) eq 0];

    y_even := RecNTT(even_part, Zq!w^2, (N div 2));
    y_odd := RecNTT(odd_part, Zq!w^2, (N div 2));
    eval_tuple := [0 : i in [1..N]];// for sidechannel I think

    for k := 0 to (N div 2)-1 do
      odd_part_sum := w^k * y_odd[k+1];
      eval_tuple[k+1] := y_even[k+1] + odd_part_sum;
      eval_tuple[k + (N div 2)+1] := y_even[k+1] - odd_part_sum;
    end for;

    return eval_tuple;
  end if;
end function;

function RecINTT(a, w, N)
  N_inverse := InverseMod(N, qb^ell);
  w_inverse := InverseMod(w, qb^ell);
  pre_output := RecNTT(a, w_inverse, N);
  return [N_inverse*i : i in pre_output];
end function;

function SquareMultiply(a, n, q) //q is the size of modulus were trying to work with
  bit := Intseq(n,2);
  k := #bit;
  b := [0 : i in [1..k]];
  b[k] := a;
  
  for i := k-1 to 1 by -1 do
    if bit[i] eq 1 then
      b[i] := (b[i+1]^2 * a) mod q;
    else;
      b[i] := (b[i+1]^2) mod q;
    end if;
  end for;

  return b[1];
end function;

function PrimitiveNthRoot(ell, N)
  return SquareMultiply(PrimitiveRoot(qb^ell), EulerPhi(qb^ell) div N, qb^ell);
end function;

function FastMult(a, b, w, N)
  coef_a := Coefficients(a);
  coef_b := Coefficients(b);
  if #coef_a lt N then
   coef_a := Eltseq(coef_a) cat [0 : i in [1..N-#coef_a]];
  end if;
  if #coef_b lt N then 
   coef_b := Eltseq(coef_b) cat [0 : i in [1..N-#coef_b]];
  end if;
  NTT_a := RecNTT(coef_a, w, N);
  NTT_b := RecNTT(coef_b, w, N);
  NTT_c := [NTT_a[i]*NTT_b[i] : i in [1..N]]; //overhead here
  coef_c := RecINTT(NTT_c, w, N);
  // c := Polynomial(Zqx, coef_c);
  c := &+[Zqx | coef_c[i]*x^(i-1) : i in [1..#coef_c]];
  return c;
end function;

function SchoolBookMult(a,b);
  coef_a := Coefficients(a);
  coef_b := Coefficients(b);
  deg_a := #coef_a - 1;
  deg_b := #coef_b - 1;
  deg_c := deg_a + deg_b;
  coef_c := [0 : i in [1..deg_c+1]];
  for j := 0 to deg_a do
    for k := 0 to deg_b do
        coef_c[j + k + 1] +:= coef_a[j + 1] * coef_b[k + 1];
    end for;
  end for;
  c := &+[coef_c[i] * x^(i-1) : i in [1..#coef_c]];
  return c;
end function;

// test encrypt / decrypt

test_task1 := true;
test_task2 := true;
test_task3 := true;
test_task4 := true;
test_task5 := false;
test_task6 := false;

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
filename := "/Users/sdheerajkumar/Desktop/magma/Project_1/basicmul.csv";
noise := BGVNoiseBound(ck, sk);
file := Open(filename, "w");
fprintf file, "%o, %o\n", 1, noise;

for k := 2 to 16 do
  ck := BGVBasicMul(ck, c1);
  noise := BGVNoiseBound(ck, sk);
  fprintf file, "%o, %o\n", k, noise;
  mk := BGVDecrypt(ck, sk);
  mt := ((mt*m1) mod f) mod p;
  print k;
  print "Test basic multiplication ", mk eq mt;
  print "Noise in basic mult", BGVNoiseBound(ck,sk);
end for;
//close(filename);
//print "dire", GetCurrentDirectory();

print "\n\n";

ck := c1;
mt := m1;
filename := "/Users/sdheerajkumar/Desktop/magma/Project_1/mul.csv";
noise := BGVNoiseBound(ck, sk);
file := Open(filename, "w");
fprintf file, "%o, %o\n", 1, noise;
for k := 2 to 16 do
  ck := BGVMul(ck, c1, ksk);
  noise := BGVNoiseBound(ck, sk);
  fprintf file, "%o, %o\n", k, noise;
  mk := BGVDecrypt(ck, sk);
  mt := ((mt*m1) mod f) mod p;
  print k;
  print "Test multiplication with key switch ", mk eq mt;
  print "Noise in mult with key switch", BGVNoiseBound(ck,sk);
end for;
//close(filename);

print "\n\n";

ck := c1;
mt := m1;
filename := "/Users/sdheerajkumar/Desktop/magma/Project_1/mul_mod.csv";
noise := BGVNoiseBound(ck, sk);
file := Open(filename, "w");
fprintf file, "%o, %o\n", 1, noise;
//for k := 2 to max_level-2 do
for k := 2 to 8 do
  ck := BGVMul(ck, c1, ksk);
  ck := BGVModSwitch(ck,1);
  noise := BGVNoiseBound(ck, sk);
  fprintf file, "%o, %o\n", k, noise;
  mk := BGVDecrypt(ck, sk);
  mt := ((mt*m1) mod f) mod p;
  print k;
  print "Test multiplication with mod switch ", mk eq mt;
  print "Noise in mult and mod switch ", BGVNoiseBound(ck,sk);
end for;
//close(filename);

print "\n\n";

// test with repeated squaring
ck := c1;
mt := m1;
filename := "/Users/sdheerajkumar/Desktop/magma/Project_1/2^k_mul_mod.csv";
noise := BGVNoiseBound(ck, sk);
file := Open(filename, "w");
for k := 1 to max_level-2 do
  ck := BGVMul(ck, ck, ksk);
  ck := BGVModSwitch(ck,1);
  noise := BGVNoiseBound(ck, sk);
  fprintf file, "%o, %o\n", k, noise;
  mk := BGVDecrypt(ck, sk);
  print k;
  mt := (mt*mt mod f) mod p;
  print "Test rep squaring mod switch multiplication ", mk eq mt;
  print "Noise in rep squaring mod switch mult", BGVNoiseBound(ck,sk);
end for;
//close(filename);

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
  //  check := Sqrt((N+3)/(2*3.14*2))*qb^(k/N+3);
  //  check_1 := Sqrt(N+25);
  //  print "check", Log(check) gt check_1;
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


