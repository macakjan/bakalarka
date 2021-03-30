from random import randint
import math

# absolute value of centered modulo of integers
def abs_mod(a, m):
    ret = a % m
    return (ret if ret <= m//2 else m-ret)

# absolute value of centered modulo of real numbers
def abs_mod_float(a, m):
    return abs(a-m*round(a/m))

# modulo of real numbers
def mod_float(a, m):
    return a-m*math.floor(a/m)

# inversion of a (mod n)
def mod_inversion(a, n):
    a, m, k1, k2 = a%n, n, 0, 1
    while a!=0:
        r, d = n%a, n//a
        k1, k2, n, a = k2, k1-d*k2, a, r
    return (k1%m if n==1 else None)

# creates an instance of HNP (represented as a tuple)
# q is the modulus (prime number)
# w_fun is a function returing 2**li (two to number of bits in i-th inequality)
# d is the number of inequalities (if not given, is determined by the function)
def create_HNP(q, w_fun=None, d=-1):
    if w_fun is None:
        w_fun = lambda i: 2**1  # one bit by default
    w_list = [w_fun(i) for i in range(d)]
    if d<0:
        s, i = 1, 1
        while s<q:
            w = w_fun(i)
            w_list.append(w)
            s *= w
            i += 1
        d = i-1
    alpha = randint(1,q-1)  # randomly choosing hidden number
    ti_list = [randint(1,q-1) for _ in range(d)]
    ui_list = [(alpha*ti_list[i]+randint(math.ceil(-q/(2*w_list[i])),
               math.floor(q/(2*w_list[i]))))%q for i in range(d)]
    return (q, ti_list, ui_list, w_list, alpha)

# transforms tuple (as returned by create_HNP) to matrix
def transform_HNP_to_matrix_C(tup):
    d = len(tup[1])
    ret = [[0]*(d+2) for _ in range(d+2)]
    for i in range(d):
        ret[i][i] = 2*tup[3][i]*tup[0]
    ret[d][d] = 1
    ret[d+1][d+1] = tup[0]
    for i in range(d):
        ret[d][i] = 2*tup[3][i]*tup[1][i]
        ret[d+1][i] = 2*tup[3][i]*tup[2][i]
    return ret

# returns boolean indicating whether given alpha is a solution to HNP
def check_HNP(tup, alpha):
    q = tup[0]
    for i in range(len(tup[1])):
        if 2*tup[3][i]*abs_mod(alpha*tup[1][i]-tup[2][i], q) >= q:
            return False
    return True

# returns boolean indicating whether given alpha is a solution to HNP
# using real numbers
def check_HNP_float(tup, alpha):
    q = tup[0]
    for i in range(len(tup[1])):
        if 2*tup[3][i]*abs_mod_float(alpha*tup[1][i]-tup[2][i], q) >= q:
            return False
    return True

# list_A and list_B must contain disjoint intervals in increasing order
# open intervals are used (endpoints not included)
def intersect_two_interval_lists(list_A, list_B):
    ret = []
    i, j, n, m = 0, 0, len(list_A), len(list_B)
    while i < n and j < m:
        low = max(list_A[i][0], list_B[j][0])
        if list_A[i][1] <= list_B[j][1]:
            top = list_A[i][1]
            i += 1
        else:
            top = list_B[j][1]
            j += 1
        if low < top:
            ret.append((low, top))
    return ret

# list_of_lists: elements are lists of disjoint intervals in increasing order
def intersect_interval_lists(list_of_lists):
    ret = [(-math.inf, math.inf)]
    for alist in list_of_lists:
        ret = intersect_two_interval_lists(ret, alist)
    return ret

# creates a list of all intervals containing real solutions
#   to one HNP inequality
# covers all solutions in the range [0,q]
# some of the returned intervals can possibly exceed this range
def make_interval_list(q, ti, ui, w):
    period = q/abs(ti)
    b = mod_float(ui/ti + period/(2*w), period)
    a = b - period/w
    k, cur, ret = 0, a, []
    while cur < q:
        ret.append((cur, cur+period/w))
        k += 1
        cur = a + k*period
    return ret

# solves HNP making and then intersecting interval lists
# returnes a sorted list of disjoint intervals covering all solutions
#   in the range (0,q): 0 as a solution will be excluded
def solve_HNP_intervals(tup):
    q = tup[0]
    return intersect_interval_lists( \
        [make_interval_list(q, tup[1][i], tup[2][i], tup[3][i]) \
         for i in range(len(tup[1]))]+[[(0,q)]])

# given an instance of HNP, returns all solutions to the first two inequalities
def solve_HNP_two_inequalities(tup):
    q, ret = tup[0], []
    c1 = math.ceil(q/(2*tup[3][0])-1)
    c2 = math.ceil(q/(2*tup[3][1])-1)
    for x in generator_HNP_two_inequalities(q, tup[1][0], tup[2][0], c1,
                                               tup[1][1], tup[2][1], c2):
        ret.append(x)
    return sorted(ret)

# yields solutions to the given two HNP inequalities (not ordered)
# c1: right side of inequality transformed to non-strict (ceil(q/2^(li+1)-1))
# uses absolute value of centered modulo (as common in HNP materials)
def generator_HNP_two_inequalities(q, t1, u1, c1, t2, u2, c2):
    t1_1 = mod_inversion(t1, q)
    u1_bar, u2_bar = u1-c1, u2-c2
    t = (t1_1*t2)%q
    u = (-u1_bar*t1_1*t2+u2_bar)%q
    for x1 in generator_HNP_one_inequality(q, t, u, 2*c2):
        if x1 <= 2*c1:
            yield ((x1+u1_bar)*t1_1)%q
        else:
            break

# yield solutions to the given HNP inequality in increasing order
# assuming 0 <= r < n/2
# does not use absolute value of centered modulo, uses classical mod
# intentionally unoptimized (aim for shorter code)
def generator_HNP_one_inequality(n, t, u, r):
    if t > n//2:
        t, u = n-t, (n-u-r)%n
    b = 0
    while True:
        while (b*t-u)%n <= r:
            yield b
            b += 1
        b += ((n-(b*t-u)%n)-1)//t+1
        if (b*t-u)%n > r:
            break
    s = ((n-1)//t+1)
    t_new = s*t-n
    for x in generator_HNP_one_inequality(t, t_new, (u-(b-1)*t)%n, r):
        yield b-1 + x*s - (x*t_new)//t


"""
# this code can be used to compare the number of integer solutions
#   of HNP to the number of intervals of real solutions
q = 1000003
li = 2
d = 10
for _ in range(4):
    tup = create_HNP(q, lambda a: 2**li, d)
    print("q: "+str(q))
    print("li: "+str(li))
    print("d: "+str(d))
    print("alpha: "+str(tup[4]))
    intervals = solve_HNP_intervals(tup)
    print(intervals)
    integer_solutions = []
    for t in intervals:
        a = math.ceil(t[0])
        b = math.floor(t[1])
        if a<=b:
            integer_solutions.append(a if a==b else (a, b))
    print(integer_solutions)
    print()
"""
