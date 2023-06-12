# SPROUTS
a **S**ymbolic **P**arser for **ROU**nd objec**TS**

## Description

Sprouts is a symbolic package written for *Wolfram Mathematica* that parses lists of ODEs corresponding to the spherical harmonics components of PDEs in spherical (and oblate spheroidal) coordinates into a set of discretizes matrices operating on the array of Chebyshev coefficients representing the set of functions to solve for. 

### features
- Fully spectral decomposition based on Gegenbauer (ultraspherical) polynomials in the radial direction
- Can deal with inhomogeneous problems of the form: $A\cdot\mathbf{x}=\mathbf{b}$, as well as *polynomial eigenvalue problems* of the form: $A_0+A_1\lambda+A_2\lambda^2+\dots$.

## Installation

### Using the Mathematica frontend

Simply download the files `sprouts.m` and `spectral.m` into your working directory and load them using 
```
<<"path/to/working/directory/spectral.m"
<<"path/to/working/directory/sprouts.m"
```

### Using the Wolfram Engine in a Jupyter notebook

coming soon.

## Acknowledgement

Made by [@jrekier](https://mathstodon.xyz/@jrekier) and team [RotaNut](https://rotanut.oma.be/)/[GRACEFUL](https://graceful.oma.be/) with support from the [**R**oyal **O**bservatory of **B**elgium](https://www.astro.oma.be/en/).


Project avatar by <a href="https://www.flaticon.com/free-icons/brussel-sprouts" title="brussel sprouts icons">Freepik - Flaticon</a>.
