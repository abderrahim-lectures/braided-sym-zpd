"""Experiment 6: search ASSOCIATIVE unital algebras (rejection sampling on
A = K.1 + V, V^2 subset V) for a zpd algebra that is not zJpd.
"""
import sys, random
sys.path.insert(0, '.')
from zpd import *
from exp3_search import alg_from_beta


def rand_associative_algebras(p, d, trials, want_assoc=None, seed=7):
    random.seed(seed)
    n = d + 1
    tested = 0
    assoc = 0
    zpd_cnt = 0
    bad = []
    for _ in range(trials):
        beta = [[[random.randrange(p) for _ in range(d)] for _ in range(d)] for _ in range(d)]
        T = alg_from_beta(p, d, beta)
        if not is_associative(n, T, p):
            continue
        assoc += 1
        dm = determined(n, T, p)
        if dm[0] != dm[1]:
            continue
        zpd_cnt += 1
        dj = determined(n, jordan_mu_p(n, T, p), p)
        if dj[0] != dj[1]:
            bad.append((beta, dm, dj))
        tested += 1
    print(f"p={p} dimV={d}: {trials} random betas -> {assoc} associative, {zpd_cnt} zpd, "
          f"{len(bad)} zpd but not zJpd", flush=True)
    for b, dm, dj in bad[:5]:
        print("   beta=", b, " product", dm, " jordan", dj)
    return bad


if __name__ == '__main__':
    p = int(sys.argv[1]); d = int(sys.argv[2]); trials = int(sys.argv[3])
    rand_associative_algebras(p, d, trials)
