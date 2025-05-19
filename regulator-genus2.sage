import scipy.integrate as spyint
import numpy as np

#Input
R.<x> = PolynomialRing(CC);  
P = x^6 + 4*x^5 + 6*x^4 + 2*x^3 + x^2 + 2*x + 1  

deg = P.degree()

roots = P.roots()

for z0 in roots:
  assert z0[1] == 1
  
assert P(-1) != 0
  
Pdiv = [ prod( [ (x - roots[j][0]) for j in range(deg) if j != i ] ) for i in range(deg) ]

const = [roots[i][0].real()*log(abs(1+roots[i][0]))/( abs(Pdiv[i](roots[i][0])) ) for i in range(deg)]
  
def f(z):
  return z.real()*log(abs(1 + z))/abs(P(z))

def correction(z, z0):
    r = abs(z-z0)
    return np.exp(- r**2) / r
  
correction_full = lambda z : sum([const[i]  * correction(z, roots[i][0]) for i in range(deg)])

f_corrected = lambda z : f(z) - correction_full(z)

f_corrected_polar = lambda r, theta : f(r*exp(I*theta)) - correction_full(r*exp(I*theta))

# Evaluate integral
r = lambda s : s / (1 - s)
integrand = lambda s, theta : f_corrected_polar(r(s), theta) * r(s) / (1 - s)**2
result, error = spyint.dblquad(
    integrand,
    0, 2*np.pi,
    0, 1
)

print("Integral result", result)
print("Corrected result", result + sum([np.pi**1.5 * const[i] for i in range(deg)]))
print("Estimated error", error)