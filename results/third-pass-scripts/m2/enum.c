/* Enumerate unital associative algebras of dimension n over F_p with basis
   1 = e_0, e_1, ..., e_{n-1}: products e_i e_j (i,j >= 1) are free, e_0 is a unit.
   Prints the structure constants of the associative ones:
   one line per algebra: n*n*n decimal numbers (mult[i][j][k]) separated by spaces.
   usage: ./enum p n [comm] */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int p, n, m, N; /* N = p^n number of elements */
static int *dig;       /* dig[u*n + l] = l-th base-p digit of u */

static int decode_idx(const int *v) {
    int s = 0, pw = 1;
    for (int l = 0; l < n; l++) { s += v[l] * pw; pw *= p; }
    return s;
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: enum p n [comm]\n"); return 1; }
    p = atoi(argv[1]);
    n = atoi(argv[2]);
    int comm = (argc > 3 && strcmp(argv[3], "comm") == 0);
    N = 1;
    for (int i = 0; i < n; i++) N *= p;
    m = n * (n - 1) * (n - 1);
    if (comm) m = n * (n - 1) * (n - 1 + 1) / 2;
    dig = malloc(sizeof(int) * N * n);
    { int v[16];
      for (int u = 0; u < N; u++) { int t = u; for (int l = 0; l < n; l++) { v[l] = t % p; t /= p; dig[u*n+l] = v[l]; } }
    }
    long long total = 1;
    for (int i = 0; i < m; i++) total *= p;
    int T[16][16];  /* T[i][j] = index of e_i e_j */
    int coords[256];
    long long count = 0, assoc = 0;
    int out[16][16][16];
    for (long long flat = 0; flat < total; flat++) {
        long long f = flat;
        for (int i = 0; i < m; i++) { coords[i] = (int)(f % p); f /= p; }
        /* build the basis multiplication */
        for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) {
            int v[16];
            if (i == 0) { for (int l = 0; l < n; l++) v[l] = 0; v[j] = 1; }
            else if (j == 0) { for (int l = 0; l < n; l++) v[l] = 0; v[i] = 1; }
            else {
                if (!comm) {
                    int base = ((i-1)*(n-1) + (j-1))*n;
                    for (int l = 0; l < n; l++) v[l] = coords[base+l];
                } else {
                    int a = i-1, b = j-1, lo = a<b?a:b, hi = a<b?b:a;
                    int base = (lo*(2*(n-1)-lo+1)/2 + (hi-lo))*n;
                    for (int l = 0; l < n; l++) v[l] = coords[base+l];
                }
            }
            T[i][j] = decode_idx(v);
        }
        count++;
        /* associativity on basis triples: (e_i e_j) e_k == e_i (e_j e_k) */
        int ok = 1;
        for (int i = 0; i < n && ok; i++) for (int j = 0; j < n && ok; j++) for (int k = 0; k < n && ok; k++) {
            int u = T[i][j], w = T[j][k];
            int lhs[16], rhs[16];
            for (int l = 0; l < n; l++) { lhs[l] = 0; rhs[l] = 0; }
            for (int l = 0; l < n; l++) {
                int c = dig[u*n+l];
                if (c) { const int *tp = dig + T[l][k]*n; for (int q = 0; q < n; q++) lhs[q] += c * tp[q]; }
                c = dig[w*n+l];
                if (c) { const int *tp = dig + T[i][l]*n; for (int q = 0; q < n; q++) rhs[q] += c * tp[q]; }
            }
            for (int q = 0; q < n; q++) if ((lhs[q]-rhs[q]) % p) { ok = 0; break; }
        }
        if (!ok) continue;
        assoc++;
        for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) {
            const int *tp = dig + T[i][j]*n;
            for (int k = 0; k < n; k++) out[i][j][k] = tp[k];
        }
        for (int i = 0; i < n; i++) for (int j = 0; j < n; j++) for (int k = 0; k < n; k++)
            printf("%d ", out[i][j][k]);
        printf("\n");
    }
    fprintf(stderr, "p=%d n=%d%s: %lld candidates, %lld associative\n", p, n, comm ? " (commutative)" : "", count, assoc);
    return 0;
}
