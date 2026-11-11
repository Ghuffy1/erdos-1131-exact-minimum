> Reproduced under Apache-2.0 from seanm27lol/erdos-1131-lean at commit `31574acf09ae50430c08da92288800fe7d26c7fd`. The title below concerns the coefficient-one asymptotic subquestion. The original author retains credit for this result and its proof.

# Erdős Problem 1131 is false

Let \(M_n\) be the infimum in the problem statement.  The conjectured
limit

\[
  \lim_{n\to\infty} n(2-M_n)=1
\]

is false.  We construct admissible configurations whose scaled defects
are eventually at least \(106/105\).

## 1. The comparison nodes

Write \(b=1/6\), and let \(T_m\) denote the Chebyshev polynomial of the
first kind.  For \(n\geq 2\), set

\[
  Q_n(x)=T_n(x)-bT_{n-2}(x).
\]

At the Chebyshev extrema \(x=\cos(k\pi/n)\),

\[
 Q_n(\cos(k\pi/n))
 =(-1)^k\left(1-b\cos(2k\pi/n)\right).
\]

The factor in parentheses is positive because \(0<b<1\).  Consecutive
values therefore have opposite signs.  Hence \(Q_n\) has a root in each
of the \(n\) disjoint intervals

\[
 \left(\cos((k+1)\pi/n),\cos(k\pi/n)\right),
 \qquad 0\leq k<n.
\]

Since \(Q_n\) has degree \(n\), these are all its roots and they are
simple.  Denote them by \(x_0,\ldots,x_{n-1}\).  They are distinct and
belong to \((-1,1)\), so they form an admissible configuration without
any appeal to attainment of the infimum.

## 2. Exact sums over the roots

For \(m\geq 0\), put

\[
 S_m=\sum_{i=0}^{n-1}T_m(x_i).
\]

The following identities are exact:

\[
\begin{aligned}
S_m&=0 &&\text{if \(m\) is odd and \(m\leq 2n-2\)},\\
S_0&=n,\\
S_{2r}&=b^r &&(1\leq r\leq n-2),\\
S_{2n-2}&=b^{n-1}+(n-1)b.
\end{aligned}
\tag{1}
\]

Here is a self-contained derivation.  Because \(Q_n\) has leading
coefficient \(2^{n-1}\),

\[
 Q_n(y)=2^{n-1}\prod_{i=0}^{n-1}(y-x_i).
\]

For \(t\neq0\), substitute \(y=(t+t^{-1})/2\) and use

\[
 T_m\!\left(\frac{t+t^{-1}}2\right)
   =\frac{t^m+t^{-m}}2.
\]

After multiplying by \(2t^n\), one obtains the polynomial identity

\[
 \prod_{i=0}^{n-1}(t^2-2x_it+1)
 =t^{2n}-bt^{2n-2}-bt^2+1.
\tag{2}
\]

For each quadratic factor, the sum of the \(m\)-th powers of its two
complex roots is \(2T_m(x_i)\).  Thus the \(m\)-th root power sum of the
polynomial in (2) is \(2S_m\).  Newton's identities applied to the
sparse monic polynomial on the right give the following recurrence when
\(n\geq3\):

\[
 p_1=0,\qquad p_2=2b,\qquad
 p_m=bp_{m-2}\quad(3\leq m\leq2n-3),
\]

and at the last needed index,

\[
 p_{2n-2}=bp_{2n-4}+(2n-2)b.
\]

These recurrences prove (1) for \(n\geq3\).  When \(n=2\), the two
coefficients of \(t^2\) in (2) coincide; directly,
\(Q_2(x)=2x^2-1-b\), so both roots satisfy \(T_2(x_i)=b\) and hence
\(S_2=2b=b^{\,1}+(2-1)b\).  Thus (1) also holds in this exceptional
case.  (Only \(n\geq7\) is used below.)

## 3. The interpolation trace identity

Put \(N=n-1\).  Define the square evaluation matrix

\[
 A_{ij}=T_j(x_i),\qquad 0\leq i,j\leq N,
\]

and the continuous and discrete Gram matrices

\[
 H_{jk}=\int_{-1}^{1}T_j(t)T_k(t)\,dt,
 \qquad R=A^{\mathsf T}A.
\]

The determinant of \(A\) is nonzero: its columns are evaluations of
polynomials of respective degrees \(0,\ldots,N\) with nonzero leading
coefficients, so its determinant is a nonzero diagonal multiple of the
Vandermonde determinant.

The \(k\)-th column of \(A^{-1}\) is consequently the vector of
Chebyshev coefficients of the \(k\)-th Lagrange cardinal polynomial.
Expanding its square, integrating, and summing over \(k\) gives the
exact identity

\[
 I_n(x_0,\ldots,x_N)
 =\operatorname{tr}(HR^{-1}).
\tag{3}
\]

The product identity \(2T_jT_k=T_{j+k}+T_{|j-k|}\), together with (1),
gives

\[
 R=\frac N2D+K,
\tag{4}
\]

where

\[
 D=\operatorname{diag}(2,1,\ldots,1,1+b)
\]

and

\[
 K_{jk}=
 \begin{cases}
 \dfrac{b^{(j+k)/2}+b^{|j-k|/2}}2,
   &j\equiv k\pmod2,\\[6pt]
 0,&j\not\equiv k\pmod2.
 \end{cases}
\tag{5}
\]

The exceptional term \((n-1)b\) in (1) is exactly what changes the last
diagonal entry of \(D\) from \(1\) to \(1+b=7/6\).

The unweighted Chebyshev integral is

\[
 \int_{-1}^{1}T_m(t)\,dt=
 \begin{cases}
 \dfrac{2}{1-m^2},&m\ \text{even},\\
 0,&m\ \text{odd}.
 \end{cases}
\]

Therefore, with

\[
 d_r=\frac1{1-4r^2},
\]

we have

\[
 H_{jk}=
 \begin{cases}
 d_{(j+k)/2}+d_{|j-k|/2},&j\equiv k\pmod2,\\
 0,&j\not\equiv k\pmod2.
 \end{cases}
\tag{6}
\]

In particular, \(|H_{jk}|\leq2\).

## 4. A uniform inverse estimate

Let

\[
 D^{-1}=\operatorname{diag}(1/2,1,\ldots,1,6/7),\qquad
 Y=\frac2N D^{-1}K,\qquad Z=(1+Y)^{-1}.
\]

This inverse exists: \(A\) is invertible, hence so is
\(R=A^{\mathsf T}A\); equation (4) factors it as
\(R=(N/2)D(1+Y)\), and \(N>0\) and the diagonal matrix \(D\) are
invertible.

For a matrix \(B\), write

\[
 \|B\|_{\infty,\mathrm{row}}
 =\max_i\sum_j|B_{ij}|.
\]

For fixed \(i\), the distance exponents \(|i-j|/2\) in (5) contribute
at most

\[
 1+2\sum_{r\geq1}b^r=\frac75.
\]

The exponents \((i+j)/2\) are distinct as \(j\) ranges over indices of
the same parity, so their contribution is at most

\[
 \sum_{r\geq0}b^r=\frac65.
\]

It follows that

\[
 \|K\|_{\infty,\mathrm{row}}\leq\frac{13}{10},
 \qquad
 \|Y\|_{\infty,\mathrm{row}}\leq\frac{13}{5N}.
\tag{7}
\]

For \(N\geq6\), the latter number is less than \(1\).  From
\(Z=1-YZ\), the maximum-row argument for a geometric inverse gives
\(\|Z\|_{\infty,\mathrm{row}}\leq2\).  Expanding once more,

\[
 R^{-1}
 =\frac2ND^{-1}
  -\frac4{N^2}D^{-1}KD^{-1}+E,
\tag{8}
\]

where

\[
 E=Y^2Z\left(\frac2ND^{-1}\right),\qquad
 \|E\|_{\infty,\mathrm{row}}
 \leq\frac{676}{25N^3}.
\tag{9}
\]

Since \(H\) has \(N+1\) rows and every entry has absolute value at most
\(2\), (9) implies

\[
 |\operatorname{tr}(HE)|\leq\frac{64}{N^2}
 \qquad(N\geq6).
\tag{10}
\]

## 5. The two first-order traces

Set

\[
 \mathcal A_N=\operatorname{tr}(HD^{-1}),\qquad
 \mathcal B_N=\operatorname{tr}(HD^{-1}KD^{-1}).
\]

The elementary telescoping identity

\[
 \sum_{r=1}^{m}d_r=-\frac{m}{2m+1}
\]

and the endpoint entries of \(D^{-1}\) give

\[
 \mathcal A_N\leq N+\frac5{14}+\frac1N.
\tag{11}
\]

For completeness, we record the lower estimate for the other trace in
the same form used by the Lean proof.  Put
\(u_r=-d_r=1/(4r^2-1)\) for \(r\geq1\).  The diagonal terms are
nonnegative, and the interior diagonal terms give

\[
 \sum_{i=1}^{N-1}
   (1+d_i)\frac{1+b^i}{2}
 \geq \frac N2-\frac34.
\tag{12}
\]

Every nonzero off-diagonal term is negative.  For a fixed row \(i\),
write

\[
 r=\frac{|i-j|}{2}\geq1,\qquad s=\frac{i+j}{2}\geq r.
\]

After dropping the endpoint weights, its absolute value is at most

\[
 \frac12(u_s+u_r)(b^s+b^r).
\]

The elementary estimates

\[
\begin{aligned}
\sum_{r\geq1}u_rb^r
  &\leq \frac13b+\frac1{15}\sum_{r\geq2}b^r
   =\frac{13}{225},\\
\sum_{\substack{0\leq j\leq N\\j\equiv i\ (2),\,j\ne i}}b^{|i-j|/2}
  &\leq\frac25
\end{aligned}
\]

use only that each positive distance occurs at most twice.  If
\(i\geq6\), then \(s\geq3\), so \(u_s\leq1/35\), while always
\(u_r,u_s\leq1/3\).  Expanding the four products above consequently
gives the row bound

\[
\sum_{\substack{0\leq j\leq N\\j\equiv i\ (2),\,j\ne i}}
  \frac12(u_s+u_r)(b^s+b^r)
\leq \frac1{15}
 +\frac13\sum_{\substack{0\leq j\leq N\\j\equiv i\ (2),\,j\ne i}}b^s.
\]

The first six rows are handled by the cruder bounds
\(|H_{ij}|\leq2/3\) and
\(\sum_jK_{ij}\leq13/10\), for a total loss at most \(26/5\).
Finally,

\[
\sum_{i=0}^{N}
 \sum_{\substack{0\leq j\leq N\\j\equiv i\ (2),\,j\ne i}}
 b^{(i+j)/2}
\leq
\left(2\sum_{r\geq0}b^r\right)^2
=\frac{144}{25}.
\]

Thus the entire off-diagonal contribution is at least

\[
\ -\frac{N+1}{15}-\frac{26}{5}-\frac{48}{25}.
\]

Combining this with (12) yields

\[
 \mathcal B_N\geq\frac{13N}{30}-13.
\tag{13}
\]

## 6. The contradiction

Combining (3), (8), and (10)--(13), for \(N\geq6\) we obtain

\[
\begin{aligned}
 I_{N+1}(x_0,\ldots,x_N)
 &\leq
 \frac2N\left(N+\frac5{14}+\frac1N\right)
 -\frac4{N^2}\left(\frac{13N}{30}-13\right)
 +\frac{64}{N^2}\\
 &=2-\frac{107}{105N}+\frac{118}{N^2}.
\end{aligned}
\tag{14}
\]

Because \(M_{N+1}\) is an infimum,

\[
 M_{N+1}\leq I_{N+1}(x_0,\ldots,x_N).
\]

If \(N\geq24780\), then \(N+1\leq2N\) and \(236/N\leq1/105\).
Equation (14) therefore implies

\[
\begin{aligned}
(N+1)(2-M_{N+1})
&\geq(N+1)(2-I_{N+1})\\
&\geq\frac{106}{105}>1.
\end{aligned}
\]

Thus the sequence in the conjecture is eventually bounded below by
\(106/105\), so it cannot converge to \(1\).  This disproves Erdős
Problem 1131 as stated.

## Lean development

The Lean source mirrors the proof above with named declarations for every
decisive step.  `README.md` records the declaration map, exact toolchain and
mathlib revision, and the clean build command.
