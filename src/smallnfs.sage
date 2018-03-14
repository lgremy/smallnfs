# This implementation works only when f[0] = x - m

P.<x> = ZZ[]

# ---------- Utilities ----------
# Produce a prime l of n bits coming from RSA-1024 and p = 2 * l + 1
def build_target(n):
    rsa1024 = 1.35066410865995223349603216278805969938881475605667027524485143851526510604859533833940287150571909441798207282164471551373680419703964191743046496589274256239341020864383202110372958725762358509643110564073501508187510676594629205563685529475213500852879416377328533906109750544334999811150056977236890927563
    l_tmp = next_prime(round(rsa1024 * 10^floor(n * log(2, 10))))
    while not (2 * l_tmp + 1).is_prime():
        l_tmp = next_prime(l_tmp)
    return (l_tmp, 2 * l_tmp + 1)

# Pseudo ideal factorization
def pseudo_ideal_facto(a, rel):
    facto = []
    for i in rel:
        if a[1] % i[0] == 0:
            facto.append(((i[0], P(0)), i[1]))
        else:
            Q.<y> = GF(i[0])[]
            for fac in Q(a).factor():
                if fac[0].degree() == 1:
                    facto.append(((i[0], P(fac[0]) - i[0]), i[1]))
    return facto

# Square and multiply (instead of power_mod, allow to compute it for univariate
# polynomial ring over ring of integers modulo a prime)
def pow_mod(a, n, f):
    if n == 0:
        return  1
    elif n == 1:
        return  a
    elif n % 2 == 0:
        return pow_mod((a * a) % f,  n / 2, f)
    else:
        return (a * pow_mod((a * a) % f, (n - 1) / 2, f)) % f

# Assert if a^(lb*(p-1)/l) == b^(la*(p-1)/l)
def assert_rat_side(a, la, b, lb, p, l):
    assert(power_mod(a, lb *  (p - 1) // l, p) == power_mod(b, la *  (p - 1) //
        l, p))

# Build the matrix associated to an ideal
def ideal_matrix(ideal):
    return matrix([[ideal[0], 0], ideal[1].coefficients(sparse=False)])

# ---------- Polynomial selection ----------
# Base m with f0 of degree 1 and lc(f0) == 1
def pol_sel(m, d, p):
    f0 = x - m
    f1 = [0] * (d + 1)
    f1[d] = p // m^d
    r = f1[d] * m^d
    for i in range(d - 1, -1, -1):
        f1[i] = (p - r) // m^i
        r = r + f1[i] * m^i
    f1 = P(f1)
    return (f0, P(f1))

# Try to build an ideal over q in the number field defined by f
def build_ideal(f, q):
    lc = f.leading_coefficient()
    lcp = f.coefficients(sparse=False)[f.degree() - 1]
    ideal = []
    # Avoid the ideals if f.discriminant() mod q == 0 or
    # if lc mod q == 0 and lcp mod q == 0
    avoid = []
    if f.discriminant() % q != 0:
        if lc % q == 0 and lcp % q != 0:
            ideal.append((q, P(0))) # q is purely projective
        if lc % q == 0 and lcp % q == 0:
            avoid.append(q)
            return (ideal, avoid)
        Q.<y> = GF(q)[]
        for fac in Q(f).factor():
            if fac[0].degree() == 1 and fac[1] == 1:
                ideal.append((q, P(fac[0]) - q))
    else:
        avoid.append(q)
    return (ideal, avoid)

# Build factor bases
def build_fb(f, B):
    avoid = []; F = []
    for i in range(len(f)):
        avoidtmp = []
        Ftmp = []
        for q in primes(B[i]):
            (ideals, avoids) = build_ideal(f[i], q)
            for k in ideals:
                Ftmp.append(k)
            for k in avoids:
                avoidtmp.append(k)
        avoid.append(avoidtmp)
        F.append(Ftmp)
    return (F, avoid)

# ---------- Relation collection ----------
# Return True if F is B-smooth and do not have factor in avoid. Return also the
# factorization, if True
def is_smooth_and_avoid(N, B, avoid):
    if N == 0:
        return (False, 0)
    if N == 1:
        return (False, 0)
    fac = N.factor()
    if fac[len(fac) - 1][0] < B:
        for f in fac:
            if f[0] in avoid:
                return (False, 0)
        return (True, fac)
    return (False, 0)

# Compute norm of a in the number field defined by f
def norm(a, f):
    return abs(a.resultant(f))

# Line sieve
# p is prime, r is positive
def line_sieve(p, r, H, L, side):
    x0 = 0
    for e1 in range(0, H[1]):
        e0 = x0
        while e0 < H[0]:
            if e0 >= -H[0]:
                L[e0 + H[0]][e1][side] = L[e0 + H[0]][e1][side] / p
            e0 = e0 + p
        e0 = x0 - p
        while e0 >= -H[0]:
            if e0 < H[0]:
                L[e0 + H[0]][e1][side] = L[e0 + H[0]][e1][side] / p
            e0 = e0 - p
        x0 = x0 + r
        if x0 >= H[0]:
            x0 = x0 - p

# Franke Kleinjung vectors
# Implementation based on the one of CADO-NFS
# (http://cado-nfs.gforge.inria.fr), see file sieve/las-plattice.h,
# function reduce_plattice_original.
# TODO: cleaner version
def reduce_qlattice(M, H0, r, h):
    a0 = -r
    b0 = h
    a1 = 0
    b1 = 1
    k = 0
    I = 2 * H0

    while b0 >= I:
        k = int(float(a0) / float(b0))
        if bool(a0 < 0) != bool(b0 < 0):
            a0 = a0 % b0
            a0 = a0 - b0
        else:
            a0 = a0 % b0
        a1 = a1 - k * b1
        if a0 > -I:
            break;
        k = int(float(b0) / float(a0))
        if bool(a0 < 0) != bool(b0 < 0):
            b0 = b0 % a0
            b0 = b0 - a0
        else:
            b0 = b0 % a0
        b1 = b1 - k * a1
        if b0 < I:
            break
        k = int(float(a0) / float(b0))
        if bool(a0 < 0) != bool(b0 < 0):
            a0 = a0 % b0
            a0 = a0 - b0
        else:
            a0 = a0 % b0
        a1 = a1 - k * b1
        if a0 > -I:
            break
        k = int(float(b0) / float(a0))
        if bool(a0 < 0) != bool(b0 < 0):
            b0 = b0 % a0
            b0 = b0 - a0
        else:
            b0 = b0 % a0
        b1 = b1 - k * a1
    k = b0 - I - a0;
    if b0 > -a0:
        if a0 == 0:
            return 0
        k = int(float(k)/ float(a0))
        b0 = b0 - k * a0
        b1 = b1 - k * a1
    else:
        if b0 == 0:
            return 0
        k = int(float(k)/ float(b0))
        a0 = a0 + k * b0
        a1 = a1 + k * b1
    assert(a0 > -I); assert(0 >= a0); assert(0 <= b0); assert(b0 < I)
    assert(a1 > 0); assert(b1 > 0)

    return (1, vector([a0, a1]), vector([b0, b1]))

# Franke-Kleinjung sieve
def lattice_sieve(p, r, H, L, side):
    reduce_qlattice()

# Arrange matrix special-q
def arrange_matrix_spq(M):
    coeff = []
    if M[0][1] < 0:
        coeff.append([-1, 0])
    else:
        coeff.append([1, 0])
    if M[1][1] < 0:
        coeff.append([0, -1])
    else:
        coeff.append([0, 1])
    M = matrix(coeff) * M
    if M[0][1] > M[1][1]:
        M.swap_rows(0, 1)
    return M

# Verify smoothness of a
def good_rel_spq(a, f, q, qside, avoid):
    fac = []
    test = True
    j = 0
    while j < len(f) and test:
        n = norm(a, f[j])
        if qside == j:
            n = n / q
        facto = is_smooth_and_avoid(n, B[j], avoid[j])
        test = test and facto[0]
        if test:
            # facto != 0
            facto = list(facto[1])
            # Add q to facto, since it is removed upper
            if qside == j:
                if q in [i[0] for i in facto]:
                    index = [i[0] for i in facto].index(q)
                    # Update the tuple by recreating it
                    facto[index] = (q, facto[index][1] + 1)
                else:
                    facto.append((q, 1))
                    if facto[len(facto) - 1][0] < facto[len(facto) - 2][0]:
                        # facto is not sorted by increasing primes
                        facto.sort(key=lambda t: t[0])
            fac.append(facto)
            j = j + 1
    return (test, fac)

# Root in q-lattice
def root_qlattice(M, i):
    inv =  M[0][0] - M[0][1] * i[1][0]
    if inv % i[0] == 0:
        return None
    return ((i[1][0] * M[1][1] - M[1][0]) * (M[0][0] - M[0][1] *
        i[1][0]).inverse_mod(i[0])) % i[0]

# Special-q + line sieve
def spq_sieve(ideal, qside, f, B, H, F, avoid, fbb, thresh, nb_rel):
    Q.<y> = GF(ideal[0])[]
    assert(Q(ideal[1]) in [fac[0] for fac in Q(f[qside]).factor()])
    M = ideal_matrix(ideal).LLL()
    M = arrange_matrix_spq(M)
    R = []
    L = []
    for i0 in range(-H[0], H[0]):
        L.append([])
        for i1 in range(0, H[1]):
            [a0, a1] = list(vector((i0, i1)) * M)
            a = a0 + a1 * x
            L[i0 + H[0]].append([norm(a, f[0]), norm(a, f[1])])
    for j in range(len(f)):
        for i in F[j]:
            if i[0] > fbb[j]:
                break
            if (i[1].degree() == 1):
                r = root_qlattice(M, i)
                if r != None:
                    line_sieve(i[0], r, H, L, j)
    for i0 in range(-H[0], H[0]):
        for i1 in range(0, H[1]):
            norms = L[i0 + H[0]][i1]
            test = True
            for j in range(len(f)):
                test = test and (norms[j] < thresh[j])
            if test:
                [a0, a1] = list(vector((i0, i1)) * M)
                if gcd(a0, a1) == 1 and a1 >= 0:
                    a = a0 + a1 * x
                    (test, fac) = good_rel_spq(a, f, ideal[0], qside, avoid)
                    if test:
                        rel = [a]
                        for j in range(len(fac)):
                            rel.append(fac[j])
                        R.append(tuple(rel))
                    if len(R) == nb_rel:
                        return R
    return R

# Remove duplicate relations
def dup(L):
    D = {}
    for i in L:
        D[i[0]] = (i[1], i[2])
    L = []
    for i in D:
        L.append((i, D[i][0], D[i][1]))
    return L


# High level function to perform relation collection
def find_rel_spq_sieve(f, B, H, F, avoid, fbb, thresh, qside, qrange):
    R = []
    q = qrange[0]
    if not q.is_prime():
        q = next_prime(q)
    fqside = f[qside]
    while q < qrange[1]:
        (ideals, _) = build_ideal(fqside, q)
        for i in ideals:
            if i[0] > fbb[qside] and i[1].degree() == 1:
                Q = spq_sieve(i, qside, f, B, H, F, avoid, fbb, thresh, -1)
                R = R + Q
        q = next_prime(q)
    return dup(R)

# ---------- Linear algebra ----------
# Number of Schirokauer maps
def nb_SM(f):
    return len(f.real_roots()) + (len(f.complex_roots()) -
            len(f.real_roots())) / 2 - 1

# Compute the Schirokauer map exponent
def sm_exp(f, l):
    Q.<y> = GF(l)[]
    return lcm([l^i[0].degree() - 1 for i in Q(f).factor()])

# Compute the Schirokauer map 
def compute_SM(a, sm_1_exp, nb_sm_1, l, f):
    Q.<y> = IntegerModRing(l^2)[]
    aq = Q(a); fq = Q(f); L = []
    tmp = list(P(pow_mod(aq, sm_1_exp, fq)) - 1)
    i = len(tmp) - 1
    while len(L) < nb_sm_1:
        L.append(Integer(tmp[i] / l))
        i = i - 1
    return L

# Row transformation
def row_trans(r, F, column_1, nb_sm_1, sm_1_exp, l, f1):
    L = [0 for i in range(len(F[0]) + len(F[1]) + column_1)]
    for ideal in pseudo_ideal_facto(r[0], r[1]):
        L[F[0].index(ideal[0])] = ideal[1]
    for ideal in pseudo_ideal_facto(r[0], r[2]):
        L[len(F[0]) + F[1].index(ideal[0])] = -ideal[1]
    if column_1 == 1:
        L[len(F[0]) + len(F[1])] = 1
    if nb_sm_1 != 0:
        L = L + compute_SM(r[0], sm_1_exp, nb_sm_1, l, f1)
    return L

# Build the matrix of relations
def build_mat(R, F, f1, l, column_1, nb_sm_1, sm_1_exp):
    M = []
    for r in R:
        L = row_trans(r, F, column_1, nb_sm_1, sm_1_exp, l, f1)
        M.append(L)
    return matrix(GF(l), M)

# Virtual logarithms
# Return all the indices such that L[i] == k
def index(L, k):     
    return [i for i in range(len(L)) if L[i] == k]

# Find not known virtual log
def not_known(K):
    nk = []
    for i in range(1, K.dimensions()[0]):
        L = list(set(list(K[i])))
        for j in L:
            if j != 0:
                nk = nk + index(list(K[i]), j)
    return nk

# Associate virtual logarithm to ideal
def associate(F, K, nk, column_1, nb_sm_1):
    V = [{}, {}]; col1 = -1; SM1 = [-1 for i in range(nb_sm_1)]
    for i in range(len(F[0])):
        if i not in nk:
            V[0][F[0][i]] = K[i]
    for i in range(len(F[1])):
        if i + len(F[0]) not in nk:
            V[1][F[1][i]] = K[len(F[0]) + i]
    if column_1 == 1:
        col1 = K[len(F[0]) + len(F[1])]
    for i in range(nb_sm_1):
        SM1[i] = K[i + len(F[0]) + len(F[1]) + column_1]
    return (V, col1, SM1)

# ---------- Individual logarithm ----------
# Compute individul logarithm of an ideal above next_prime(B[0]) in K0 (always
# exists)
def ind_log_0(f, B, H, F, avoid, V, col1, fbb, thresh, SM1, sm_1_exp, l):
    q = next_prime(B[0])
    # Assume we can have a relation with the previous setting
    spq = build_ideal(f[0], q)[0][0]
    # Take the first relation
    r = spq_sieve(spq, 0, f, B, H, F, avoid, fbb, thresh, -1)[0]
    pseudo_ideal_facto_0 = pseudo_ideal_facto(r[0], r[1])
    coeff_spq = Integer(pseudo_ideal_facto_0[[i[0] for i in
        pseudo_ideal_facto_0].index(spq)][1])
    vlog = (-(sum([V[0][i[0]] * i[1] for i in pseudo_ideal_facto_0 if i[0] in
        V[0].keys()])) + (sum([V[1][i[0]] * i[1] for i in
            pseudo_ideal_facto(r[0], r[2])])) - col1)
    if len(SM1) != 0:
        sm = compute_SM(r[0], sm_1_exp, len(SM1), l, f[1])
        for i in range(len(SM1)):
            vlog = vlog - sm[i] * SM1[i]
    vlog = vlog % l
    vlog = (vlog * coeff_spq.inverse_mod(l)) % l
    V[0][spq] = vlog

# ---------- Data ----------
# l = 3141592653589793238462773; p = 2 * l + 1; d = 3; B = [4096, 4096]
# H = [2^7, 2^7]; fbb = [B[0] // 4, B[1] // 4]; thresh = [B[0]^3, B[1]^3]
(l, p) = build_target(20); d = 2; B = [2^7, 2^7]; H = [2^5, 2^5]
fbb = [B[0] // 4, B[1] // 4]; thresh = [B[0]^3, B[1]^3]
# (l, p) = build_target(10); d = 3; B = [2^7, 2^7]; H = [2^5, 2^5]
# fbb = [B[0] // 4, B[1] // 4]; thresh = [B[0]^3, B[1]^3]

# ---------- Main ----------
def main(d, p, B, H, l, fbb, thresh):
    print("Polynomial selection")
    m = floor(p^(1/(d + 1)))
    f = pol_sel(m, d, p)

    # Build sieve bases
    (Fbb, avoid) = build_fb(f, fbb)
    # Build factor bases
    (F, avoid) = build_fb(f, B)

    print("Relation collection")
    # TODO: stop relation collection when len(R) >> len(F[0]) + len(F[1])
    R = find_rel_spq_sieve(f, B, H, Fbb, avoid, fbb, thresh, 1, [fbb[1], B[1]])
    assert(len(R) >= len(F[0]) + len(F[1]))

    print("Linear algebra")
    sm_1_exp = sm_exp(f[1], l)
    nb_sm_1 = nb_SM(f[1])
    column_1 = 0
    # Add a column of 1 that resprents the ideals that divide the leading
    # coefficient
    if f[1].leading_coefficient() != 1:
        column_1 = 1
    M = build_mat(R, F, f[1], l, column_1, nb_sm_1, sm_1_exp)
    K = M.right_kernel().basis_matrix()

    # Virtual logarithm
    nk = not_known(K)
    K = K[0]
    (V, col1, SM1) = associate(F, K, nk, column_1, nb_sm_1)

    print("Individual logarithm")
    ind_log_0(f, B, H, F, avoid, V, col1, fbb, thresh, SM1, sm_1_exp, l)
    # Assert on rational side
    for i in range(len(V[0].keys())):
        for j in range(i + 1, len(V[0].keys())):
            assert_rat_side(Integer(V[0].keys()[i][0]),
                    Integer(V[0][V[0].keys()[i]]), Integer(V[0].keys()[j][0]),
                    Integer(V[0][V[0].keys()[j]]), p, l)

    return (V, col1, SM1)

# ---------- Run ----------
# print(main(d, p, B, H, l, fbb, thresh))
