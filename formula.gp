/* ============================================================================
   S(n) = sum_{l=0}^{n-1} (l^2 mod n),  computed by the class-number closed form

      S(n) = n(n-m)/2
             - 2n * sum_{D<0 fundamental, D|n} (h_D / w_D)
                    * sum_{D s^2 | n} s * prod_{p|s} ( 1 - (1/p)(D/p) ),

   where n = m^2 d with d squarefree (so m = square-part root),
   h_D = class number of Q(sqrt D),  w_D = #units in {6,4,2},
   and (D/p) is the Kronecker symbol.

   PARI/GP builtins used: core, isfundamental, qfbclassno, kronecker, factor.
   ============================================================================ */

S(n) =
{
  my(m, res, cls, D, h, w, inner, fs, fa, pp, ee);
  m   = sqrtint(n \ core(n));               \\ n = m^2 * core(n);  m = square-part root
  res = n*(n-m)/2;                          \\ condensed main + squareful term
  cls = 0;
  fordiv(n, g,                              \\ g = |D| ranges over the divisors of n
    D = -g;
    if(isfundamental(D),                    \\ keep only negative fundamental discriminants
      h = qfbclassno(D);                    \\ class number  h_{Q(sqrt D)}
      w = if(D == -3, 6, if(D == -4, 4, 2)); \\ number of units  w_D
      inner = 0;
      fordiv(m, s,                           \\ every valid s divides m (the square-part root)
        if(n % (g*s^2) == 0,                 \\ keep s with D*s^2 | n
          /* f(s) = s * prod_{p|s}(1 - (1/p)(D/p)) = prod_{p^e || s}(p^e - (D/p) p^(e-1)) */
          fs = 1;  fa = factor(s);
          for(i = 1, #fa~,
            pp = fa[i,1];  ee = fa[i,2];
            fs *= pp^ee - kronecker(D, pp) * pp^(ee-1)
          );
          inner += fs
        )
      );
      cls += (h/w) * inner
    )
  );
  res - 2*n*cls
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
