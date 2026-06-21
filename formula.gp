/* ============================================================================
   S(n) = sum_{l=0}^{n-1} (l^2 mod n),  computed by the class-number closed form

      S(n) = n(n-m)/2
             - 2n * sum_{Delta<0 a discriminant, Delta | n}  h(Delta) / w(Delta),

   where n = m^2 d with d squarefree (so m = square-part root),
   Delta runs over the NEGATIVE discriminants dividing n -- i.e. Delta == 0 or 1
   (mod 4) with -Delta | n -- fundamental AND non-fundamental alike,
   h(Delta) = class number of the order of discriminant Delta (the form class
              number; for fundamental Delta this is the class number of Q(sqrt Delta)),
   w(Delta) = number of units of that order, in {6, 4, 2}.

   This is the collapsed form of the earlier double sum: by the class-number
   formula for non-maximal orders (Cox, Primes of the form x^2+ny^2, Thm 7.24),
      (h_D / w_D) * s * prod_{p|s}(1 - (1/p)(D/p))  =  h(D s^2) / w(D s^2),
   so summing the fundamental-discriminant term over all conductors s is the same
   as summing h(Delta)/w(Delta) over every negative discriminant Delta = D s^2 | n.

   PARI/GP builtins used: core, qfbclassno.
   ============================================================================ */

S(n) =
{
  my(m, acc, D, h, w);
  m   = sqrtint(n \ core(n));               \\ n = m^2 * core(n);  m = square-part root
  acc = 0;
  fordiv(n, delta,                          \\ delta = -Delta ranges over the divisors of n
    D = -delta;
    if(D % 4 == 0 || D % 4 == 1,            \\ keep negative discriminants: Delta == 0,1 (mod 4)
      h = qfbclassno(D);                    \\ class number of the order of discriminant Delta
      w = if(D == -3, 6, if(D == -4, 4, 2)); \\ number of units  w(Delta)
      acc += h/w
    )
  );
  n*(n-m)/2 - 2*n*acc                        \\ condensed elementary part minus the class-number sum
}

/* direct definition, for testing */
Sbrute(n) = sum(k = 0, n-1, k^2 % n);

/* self-test: compare the closed form with the direct sum */
selftest(N = 2000) =
{
  my(bad = 0);
  for(n = 2, N,
    if(S(n) != Sbrute(n),
      print("MISMATCH at n=", n, ":  closed=", S(n), "  direct=", Sbrute(n));
      bad = 1; break
    )
  );
  if(!bad, print("OK: S(n) == Sbrute(n) for all 2 <= n <= ", N));
  !bad
}
