from random import shuffle
from time import strftime

# In:  given element g in Fq ~= Fp[x]/f as a finite field element
# Out: find the polynomial in Fp[x] corresponding to the embedding of g
def embed(g, e):
    # getting basic information about the group G
    p = g.base_ring().order()
    Fp = GF(p)
    Fq = g.parent()
    f = Fq.modulus()
    d = f.degree()
    q = p^d
    R = f.parent()
    pi = Fq.convert_map_from(R)
    if g == Fq.zero():
        return R.zero()
    # rename the variable of g to that of B as pg
    # pg = rename_var(g.polynomial(), f)
    rn = R.convert_map_from(g.polynomial().parent())
    pg = rn(g.polynomial())
    # begin computing
    F = pg
    for j in xrange(1, e):
        A = R.quo(f^(j+1))
        phi = A.coerce_map_from(R)
        P = pi(-((((phi(F)^(q-1)).lift()-1).quo_rem(f^j))[0]))
        Q = ((q-1)*(pi(F))^(q-2))^(-1)
        aj = rn((P*Q).polynomial())
        F += aj*f^j
    return F

# In:  an element alpha in A = (Fp[x]/f^e)*, p >= e
# Out: decomposition of alpha as a list of integers:
# alpha = [[a0], [a1, ..., aD]]
def decompose(alpha, dlog=False):
    # getting parameters of the ground algebra
    C = []
    p = alpha.base_ring().order()
    A = alpha.parent()
    y = A.gen()
    h = A.modulus()
    fct = h.factor()
    f = fct[0][0]
    e = fct[0][1]
    if p < e:
        print('Warning: p < e, decomposition is currently unavailable.')
        return C
    d = f.degree()
    R = f.parent()

    # decompose eta:
    pi = A.coerce_map_from(R)
    Fq.<a> = GF(p**d)
    mu = Fq.convert_map_from(R)
    eta = mu(alpha.lift().mod(f))

    # the large component - classic discrete-log problem
    if dlog:
        C.append([eta.log(Fq.gen())])
    else:
        C.append([])
    eta = pi(embed(eta, e))
    kappa = eta^(-1) * alpha

    # decompose kappa:
    L = []
    for j in xrange(1, e):
        beta = kappa.lift().mod(f^(j+1))
        l = (beta-1).quo_rem(f^j)[0].list()
        fbar = pi(f)
        gamma = A.one()
        for k in xrange(len(l)):
            gamma *= (1+y^k*fbar^j)^(l[k])
        while len(l) < d:
            l.append(0)
        L.extend(l)
        kappa *= gamma^(-1)
    C.append(L)
    return C


# Input: p, f, e, c, where deg f = d irreducible
# Output: a generating set of (Fp[x]/f^e)* of size p^c with c|d
def genset(p, f, e, c=None):
    if not c:
        c = find_c(p, f, e)
    A = f.parent().quo(f^e)
    K = GF(p^c)
    d = f.degree()
    Fq.<alpha> = GF(p^d, modulus=f)
    h = Hom(K, Fq).list()[0]
    phi = A.coerce_map_from(f.parent())
    xbar = A.gen()
    S = [xbar+phi(embed(h(s), e)) for s in K]
    return [s for s in S if s.is_unit()]


# Find the size of the genset
def genset_size(p, d, e, c=None):
    f = GF(p)[x].irreducible_element(d)
    S = genset(p, f, e, c)
    return len(S)


# In:  S a set of elements in A = (Fp[x]/f^e)*
# Out: Whether or not S is a generating set of A
def is_genset(S):
    M, N = [], []
    p, e, d = None, None, None
    for s in S:
        if s.is_unit():
            p = s.base_ring().order()
            A = s.parent()
            h = A.modulus()
            fct = h.factor()
            f = fct[0][0]
            e = fct[0][1]
            d = f.degree()
            break
    N = [decompose(s)[1] for s in S]
    M = matrix(GF(p), N)
    if M.rank() == d*(e-1):
        return True
    return False


# find the smallest c, s.t. c|d and sqrt(p^c) > d*e/c-1 
def find_c(p, f, e):
    d = f.degree()
    for c in divisors(d):
        if p^c > (d*e/c-1)^2:
            return c
    return d


# In: p, f, e, where deg f = a perfect power b^w
# Out: A random small subset R of S (where |S|=p^c) that gen A*
# precision: output set can be of size p^{r+prec}
def genset_random(p, f, e, precision=0.1):
    d = f.degree()
    c = find_c(p, f, e)
    A = f.parent().quo(f^e)
    K = GF(p^c)
    Fq.<alpha> = GF(p^d, modulus=f)
    h = Hom(K, Fq).list()[0]
    phi = A.coerce_map_from(f.parent())
    xbar = A.gen()

    R = []
    N = []
    M = None
    r = 1.0
    pK = K.list()
    shuffle(pK)
    for k in pK:
        s = xbar+phi(embed(h(k), e))
        if s.is_unit():
            R.append(s)
            N.append(decompose(s)[1])
            if len(N) >= p^r:
                M = matrix(GF(p), N)
                if M.rank() >= d*(e-1):
                    return R 
                r += precision
    return R

# IN: p: a prime number, d>=1 the degree of f, e>=1 an integer
# OUT: the order of the multiplicative group (Fp[x]/f^e)*
def group_order(p, d, e):
    return (p^d-1)*(p^(d*(e-1)))


def run_experiment(P, E, D, file="log.txt"):
    for d in D:
        for e in E:
            for p in P:
                f = GF(p)[x].irreducible_element(d)
                S = genset(p, f, e)
                R = genset_random(p, f, e)
                c = find_c(p, f, e)
                r = log(len(R), p).n()
                print(strftime('%D %H:%M:%S') + ' p={0}, e={1}, d={2}, c={3}, r={4}'.format(p, e, d, c, r))
                with open(file, 'a') as fs:
                    fs.write(strftime('%D %H:%M:%S') + ' p={0}, e={1}, d={2}, c={3}, r={4}\n'.format(p, e, d, c, r))
                    fs.close()


#def run_experiments(file="log.txt"):
#    D = [64, 128]
#    run_experiment([5, 11, 17, 23], [5], D, file)
#    run_experiment([13], [3, 6, 9, 12], D, file)


# Input: a list where each entry is an element from  ZZ mod m for some integer m
# Output: an integer == writing as a number with base m
def list_value(l):
    if len(l) == 0:
        return 0
    b = l[0].parent().order()
    mag = Integer(1)
    val = Integer(0)
    for i in xrange(len(l)-1, -1, -1):
        val += (l[i].lift()) * mag
        mag *= b
    return val


# Return the list of all polynomials in Fp[x] corresponding to elements of A=Fp[x]/f^e
# If units_only=True, then return only elements in A*
def elements(p, f, e, units_only=False):
    return elements_iter(p, f, e-1, units_only)

def elements_iter(p, f, it, units_only=False):
    d = f.degree()
    R = f.parent()
    Fq = GF(p^d, f.variable_name(), modulus=f)
    if it == 0:
        if units_only:
            return [a.polynomial() for a in Fq if a.is_unit()]
        else:
            return [a.polynomial() for a in Fq]
    else:
        S = elements_iter(p, f, it-1, units_only)
        T = []
        for s in S:
            T.extend([s+a.polynomial()*f^it for a in Fq])
        return T


# Construct the Cayley expander over (Fp[x]/f^e)* of degree p^c
def cayley_graph(p, f, e, c=None):
    S = genset(p, f, e, c)
    d = {}
    A = S[0].parent()
    R = f.parent()
    phi = A.coerce_map_from(R)
    L = [phi(a) for a in elements(p, f, e, True)]
    for a in L:
        d[a] = [a * s for s in S]
    return DiGraph(d)


# Eigenvalue of cayley_graph(p, f, e, c)
# sorted in decreasing order
def eigenvalues(p, f, e, c=None, absolute=False):
    G = cayley_graph(p, f, e, c)
    A = G.adjacency_matrix()
    if absolute:
        E = [e.abs().n() for e in A.eigenvalues()]
    else:
        E = [e.n() for e in A.eigenvalues()]
    Esrt = sorted(E, reverse=True)
    return Esrt


# spectral gap
def spectral_gap(p, d, e, c=None):
    f = GF(p)[x].irreducible_element(d)
    E = eigenvalues(p, f, e, c, True)
    k = len(E)
    return E[0]-E[1]


# diameter
def diameter(p, d, e, c=None):
    f = GF(p)[x].irreducible_element(d)
    G = cayley_graph(p, f, e, c)
    return G.diameter()


# Input: p, e, f, c, where deg f = d irreducible
# Output: random walk matrix of cayley(G, S) with |S|=p^c
def proj_rw_matrix(p, f, e, c=None, save=None):
    d = f.degree()
    N = p^d
    E = {}
    D = [list_value(decompose(s)[1],2) for s in genset(p, f, e, c)]
    deg = len(D)
    for i in xrange(N):
        for j in D:
            E[(i, i^^j)] = 1.0/deg
    A = matrix(RR, N, E, sparse=True)
    if save:
        with open(save, 'w') as of:
            for k in E.keys():
                of.write('{0},{1}\n'.format(k[0], k[1]))
            of.close()
    return A

# Input: M: random walk matrix, t: number of steps
# Output: v: probability distribution vector
def rw(M, t, save=False, output=None):
    N = M.dimensions()[0]
    v = vector(RR, N, {0:1.0}, sparse=False)
    for i in range(t):
        v = v*M
    if save:
        of = open(output, 'w')
        for x in v:
            of.write('{0}\n'.format(x))
        of.close()
    return v

                    


