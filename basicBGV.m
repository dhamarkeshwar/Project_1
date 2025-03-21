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

sk, pk := BGVKeyGen();
m := RandomMessagePol();
c := BGVEncrypt(m,pk);
mdec := BGVDecrypt(c,sk);
print "Test encrypt / decrypt ", m eq mdec;
print "Noise in fresh ct", BGVNoiseBound(c,sk);

// test addition 
m1 := RandomMessagePol();
c1 := BGVEncrypt(m1,pk);
m2 := RandomMessagePol();
c2 := BGVEncrypt(m2,pk);
// // c3 := BGVAdd(c1,c2);
// m3 := BGVDecrypt(c3, sk);
// print "Test addition ", m3 eq (m1+m2) mod p;
// print "Noise in addition", BGVNoiseBound(c3,sk);

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

// // test basic mult 
// c3 := BGVBasicMul(c1, c1);
// m3 := BGVDecrypt(c3, sk);
// print "Test basic multiplication ", m3 eq ((m1*m1) mod f) mod p;
// print "Noise in basic mult", BGVNoiseBound(c3,sk);

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
//test for CRT

// A := [Random(Fp) : i in [1..N]];
// B := [Random(Fp) : i in [1..N]];
// // print "polynomial factor", fs[1];
// a := BGVEncode(A, fs);
// b := BGVEncode(B, fs);

// asumb := BGVDecode(a+b, fs);
// aprodb := BGVDecode((a*b) mod Fpz ! f, fs);

// print "Test additive homomorphism ", asumb eq [A[i] + B[i] : i in [1..N]];
// print "Test multiplicative homomorphism ", aprodb eq [A[i]*B[i] : i in [1..N]];

// Task 4



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

// skrec := BGVTrivialKeyRecovery(sk);
// print "Trivial key recovery works ", skrec eq sk;


// ksk := BGVKeySwitchingKeyGen(sk^2 mod f, sk);
// ck := c1;
// mt := m1;
// for k := 2 to 16 do
//   ck := BGVMul(ck, c1, ksk);
//   mk := BGVDecrypt(ck, sk);
//   mt := ((mt*m1) mod f) mod p;
//   print k;
//   print "Test modified multiplication ", mk eq mt;
//   print "Min elt", Minimum(Coefficients(BGVPartialDecrypt(ck, sk))) le 0;
//print "Min elt f", Minimum(Coefficients(-x^2+5))[1];
f := -x^2 + 5;
min_coeff, _ := Minimum(Coefficients(f)); // Extract only the coefficient value
print "Min elt f", min_coeff;

//   print "Noise in basic mult", BGVNoiseBound(ck,sk);
// end for;

// function BGVBorder_singlecoeff(c,sk)// this is only for cipher with two coefficients
//   temp := 0;
//   cipher_1 := c[1][1];
//   cipher_2 := c[1][2];
//   intermediate_cipher := <[cipher_1,cipher_2],c[2]>;
//   ksk := BGVKeySwitchingKeyGen(sk^2 mod f, sk);
//   min_coeff, _ := Minimum(Coefficients(BGVPartialDecrypt(intermediate_cipher, sk)));
//   print "is initial min_coeff less than zero", min_coeff lt 0;
//   print "min_coeff is", min_coeff;
//   while min_coeff ge 0 do
//     intermediate_cipher := BGVMul(intermediate_cipher,intermediate_cipher,ksk);
//     min_coeff, _ := Minimum(Coefficients(BGVPartialDecrypt(intermediate_cipher, sk)));
//     temp := temp + 1; //for number of partial decryption calls
//   end while;
//   return <intermediate_cipher,temp>;
// end function;

// // // print "c1", c1[1][1];
// // // print "constant coeff", Coefficient(c1[1][1],0);
// // // temp := x+1;
// // // print "add", temp+1;
// print "BGVBorder_singlecoeff debug", BGVBorder_singlecoeff(c1,sk);
// print "is c1 equal to the derived cipher, then not successful", c1 eq BGVBorder_singlecoeff(c1,sk)[1];
// print "c1 level equal to max level?", c1[2] eq max_level;
// temp, _ := Minimum(Coefficients(BGVPartialDecrypt(c1,sk)));
// print "min_coeff and position of min_coeff in c1", Minimum(Coefficients(BGVPartialDecrypt(c1,sk)));
// print "temp", dq+temp;


// print "basic check", Minimum(Coefficients(-2*x+1));
// print "prime p = ", p;
// print "minumum of coeffs", Minimum(Coefficients(c1[1][1]));
// print "maximum of coeffs", Maximum(Coefficients(c1[1][1]));
// print "is min greater than max", Minimum(Coefficients(c1[1][1])) gt Maximum(Coefficients(c1[1][1]));
//print "seq", Min(Eltseq(c1[1][1]));

//function BGVActiveAttack(pk,sk)


// Task 6

function RecNTT(a, w, N)
  if N eq 1 then 
    return [a[1]];
  else;
    even_part := [a[i] : i in [1..#a] | (i mod 2) eq 1];
    odd_part := [a[i] : i in [1..#a] | (i mod 2) eq 0];

    y_even := RecNTT(even_part, w^2 mod dq, (N div 2));
    y_odd := RecNTT(odd_part, w^2 mod dq, (N div 2));
    eval_tuple := [0 : i in [1..N]];// for sidechannel I think

    for k := 0 to (N div 2)-1 do
      odd_part_sum := w^k * y_odd[k+1];
      eval_tuple[k+1] := (y_even[k+1] + odd_part_sum) mod dq;
      eval_tuple[k + (N div 2)+1] := (y_even[k+1] - odd_part_sum) mod dq;
    end for;

    return eval_tuple;
  end if;
end function;

function RecINTT(a, w, N)
  N_inverse := InverseMod(N, dq);
  w_inverse := InverseMod(w, dq);
  pre_output := RecNTT(a, w_inverse, N);
  return [(N_inverse*i) mod dq : i in pre_output];
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
  for i := 1 to N-#coef_a do
    Append(~coef_a, 0);
  end for;
  for i := 1 to N-#coef_b do
    Append(~coef_b, 0);
  end for;
  NTT_a := RecNTT(coef_a, w, N);
  NTT_b := RecNTT(coef_b, w, N);
  NTT_c := [(NTT_a[i]*NTT_b[i]) mod dq : i in [1..N]];
  coef_c := RecINTT(NTT_c, w, N);
  c := &+[coef_c[i] * x^(i-1) : i in [1..#coef_c]];
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


M := 2^5;

a := Zx![Z | Random(M-1) : i in [1..M]];
b := Coefficients(a);
w := SquareMultiply(PrimitiveRoot(dq), EulerPhi(dq) div M, dq);

print "Is NTT successful? ", b eq RecINTT(RecNTT(b, w, M), w, M);
print "school_book working? ", SchoolBookMult(x+1,x^2+2);

print "falt mul ", FastMult(x+1, x^2+2, w, M);
