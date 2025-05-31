# Regulator integral for JacobiMotive([1/5,1/5,1/5],[3/5])
import scipy.integrate as spyint
import numpy as np

norm = pow(4,-0.2)
poles = [np.exp(2*np.pi*i*1j/5) for i in range(5)]

def f(z):
    return z * np.log(abs(1 + norm*z))/abs(1 - z**5)

def log_correction(z):
    return (-1) * norm**4 * np.log(abs(1 + norm * z))/abs(1 + norm**5) * np.exp(-(abs(z + 1/norm))**2)

def correction(z):
    return log_correction(z) + 1/5 * sum([pole * np.log(abs(1 + norm*pole))/abs(z - pole) * np.exp(-(abs(pole - z))**2)  for pole in poles])

def integrand(x, y):
    return f(x + 1j * y) - correction(x + 1j * y)

result, error = spyint.nquad(
    integrand,
    [[-np.inf, np.inf], [-np.inf, np.inf]],
    opts = {'limit' : 150, 'epsabs' : 1e-15, 'epsrel' : 1e-15}
    )

print(f"Integral result: {result}")
print(f"Integral error: {error}")

# theoretical correction term
corrtheo = 2.2939191123576945630602921547426653256868863280650223210405780574138147246831173609465756813381080090898609450998108906666552385737558677424111767775017624792888258379628674026142557860329913505320239

# regint = I*20/sqrt(5)
regint = (result + corrtheo)*norm**3/(2*np.pi)

# regint2 = I*20/sqrt(5)
regint2 = (result + corrtheo)*norm**3/(2*np.pi)*20/np.sqrt(5)

# Lval = L'(j[1,1,1,2],1) computed using Magma
Lval = 1.16611388707124780312439139002 

print(f"Regulator integral I: {regint}")
print(f"I*20/sqrt(5): {regint2}")
print(f"L-value: {Lval}")
print(f"Difference: {regint2 - Lval}")


