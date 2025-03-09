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
  for i := 1 to max_level do
    temp := g mod qb^i;
    muli := ksk[i];
    Append (~cs,[((muli[1]*temp) mod f) mod qb^i,((muli[2]*temp) mod f) mod qb^i]);
  end for;
  temp := cs[1];
  for i := 2 to #cs do
    temp := [temp[1]+cs[i][1],temp[2]+cs[i][2]];
  end for;
  return <temp,max_level>;
end function;

function BGVMul(c_1,c_2,ksk)
  cs := BGVBasicMul(c_1,c_2); // Gives 3 component cipher
 // print "cs", cs;
  result := <[cs[1][1],cs[1][2]],cs[2]>; // First 2 cipher components
  cs_1 := BGVKeySwitch(cs[1][3],cs[2],ksk); 
  // temp := &+cs_1; // shortcut to add lists, &+ from chatgpt
  return BGVAdd(result,cs_1);
end function;

// generating ksk and testing mult
ksk := BGVKeySwitchingKeyGen(sk^2 mod f, sk);
c3 := BGVMul(c1, c1, ksk);
m3 := BGVDecrypt(c3, sk);
print "Test multiplication with key switch", m3 eq ((m1*m1) mod f) mod p;
print "Noise in mult with key switch", BGVNoiseBound(c3,sk);

// ck := c1;
// mt := m1;
// for k := 2 to 16 do
//   ck := BGVMul(ck, c1, ksk);
//   mk := BGVDecrypt(ck, sk);
//   mt := ((mt*m1) mod f) mod p;
//   print k;
//   print "Test multiplication with key switch ", mk eq mt;
//   print "Noise in mult with key switch", BGVNoiseBound(ck,sk);
// end for;



