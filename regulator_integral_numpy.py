import scipy.integrate as spyint
import numpy as np
import scipy as sp

# f : a list of rational numbers, corresponding to the polynomial f[0] * x**n + ... + f[n], where n = 5 or n = 6.
# a : a rational number
# Compute the integral log|1 + a| Re(z) /|f(z)| over the complex plane
def regulator_integral(f, a = 1):
    deg = len(f) - 1
    assert deg == 5 or deg == 6
    assert np.polyval(f, -a) != 0

    roots = np.roots(f)
    fder = np.polyder(f)
    const = [roots[i].real*np.log(np.abs(a + roots[i]))/np.abs(np.polyval(fder, roots[i]))  for i in range(deg)]
    
    correction = lambda z, z0 : np.exp(- np.abs(z - z0)**2) / np.abs(z - z0)
    correction_full = lambda z : sum([const[i]  * correction(z, roots[i]) for i in range(deg)])
    f_corrected = lambda z : z.real * np.log(np.abs(a + z))/np.abs(np.polyval(f, z)) - correction_full(z)

    # Evaluate integral
    r = lambda s : s / (1 - s)
    integrand = lambda s, theta : f_corrected(r(s)*np.exp(theta*1j)) * r(s) / (1 - s)**2
    result, error = spyint.nquad(
        integrand,
        [[0, 1], [0, 2*np.pi]],
        opts = {'limit' : 80, 'epsabs' : 1e-10, 'epsrel' : 1e-10}
    )

    return result + sum([np.pi**1.5 * const[i] for i in range(deg)]), error

# f : a list of rational numbers, corresponding to the polynomial f[0] * x**n + ... + f[n]
# Compute the period matrix of the hyperelliptic curve y^2 = f(x)
# returns 2g x g matrix, where the ith row is given by the integrals of x^i dx/y over the line segments joining the first 2g + 1 roots of f.
def period_matrix(f):
    deg = len(f) - 1
    g = int((deg - 1)/2)

    roots = np.roots(f)
    roots.sort() # sort roots to avoid cycles intersecting each other
    
    periods = np.full((2*g, g), 1j) #initialize matrix of complex numbers

    for i in range(g):
        for j in range(2*g):
            integrand = lambda t : (roots[j + 1] - roots[j])*((1 - t)*roots[j] + t*roots[j + 1])**i/np.sqrt(np.polyval(f, (1 - t) * roots[j] + t*roots[j + 1]))
            resre, _ = spyint.quad( lambda t : integrand(t).real, 0, 1)
            resim, _ = spyint.quad( lambda t : integrand(t).imag, 0, 1)
            periods[j, i] = resre + resim*1j
    
    return periods

#Computes c^+(H^1(X)), where X is the hyperelliptic curve y^2 = f(x) 
def cplus(f):
    periods = period_matrix(f)
    P, L, U = sp.linalg.lu(periods.real)
    return np.linalg.det(P)*np.linalg.det(U)

#Computes c^-(H^1(X)), where X is the hyperelliptic curve y^2 = f(x) 
def cminus(f):
    periods = period_matrix(f)
    P, L, U = sp.linalg.lu(periods.imag)
    return np.linalg.det(P)*np.linalg.det(U)