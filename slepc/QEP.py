import sys, slepc4py
slepc4py.init(sys.argv)
from petsc4py import PETSc
from slepc4py import SLEPc
import numpy as np
import scipy.io as sio
import scipy.sparse as ss
from timeit import default_timer as timer
import os

maxit = 1000
tol = 1e-15
nev = 3

opts = PETSc.Options()

# load the three matrices 
mtx = sio.mmread("./A0.mtx")
mtx = ss.csr_matrix(mtx)

nr, nc = mtx.shape
A0 = PETSc.Mat().create()
A0.setSizes([nr, nc])
A0.setFromOptions()
A0.setUp()

rstart, rend = A0.getOwnershipRange() # you only need to do that once (all matrices have same size)

indptr = mtx[rstart:rend,:].indptr
indices = mtx[rstart:rend,:].indices
data = mtx[rstart:rend,:].data
del mtx

A0.setPreallocationCSR(csr=(indptr,indices))
A0.setValuesCSR(indptr,indices,data)
A0.assemble()
del indptr, indices, data

mtx = sio.mmread("./A1.mtx")
mtx = ss.csr_matrix(mtx)

nr, nc = mtx.shape
A1 = PETSc.Mat().create()
A1.setSizes([nr, nc])
A1.setFromOptions()
A1.setUp()

rstart, rend = A1.getOwnershipRange()

indptr = mtx[rstart:rend,:].indptr
indices = mtx[rstart:rend,:].indices
data = mtx[rstart:rend,:].data
del mtx

A1.setPreallocationCSR(csr=(indptr,indices))
A1.setValuesCSR(indptr,indices,data)
A1.assemble()
del indptr, indices, data

mtx = sio.mmread("./A2.mtx")
mtx = ss.csr_matrix(mtx)

nr, nc = mtx.shape
A2 = PETSc.Mat().create()
A2.setSizes([nr, nc])
A2.setFromOptions()
A2.setUp()

rstart, rend = A2.getOwnershipRange()

indptr = mtx[rstart:rend,:].indptr
indices = mtx[rstart:rend,:].indices
data = mtx[rstart:rend,:].data
del mtx

A2.setPreallocationCSR(csr=(indptr,indices))
A2.setValuesCSR(indptr,indices,data)
A2.assemble()
del indptr, indices, data


# set up solver
E = SLEPc.PEP(); E.create()

E.setOperators([A0,A1,A2])
E.setProblemType(SLEPc.PEP.ProblemType.GENERAL)

# default pivot target and criterion
tau = 1.+0.*1j
E.setWhichEigenpairs(SLEPc.PEP.Which.TARGET_IMAGINARY)
E.setTarget(tau)

# override options from commande line
E.setFromOptions()

tic = timer()
E.solve()
toc2 = timer()

Print = PETSc.Sys.Print

Print()
Print("******************************")
Print("*** SLEPc Solution Results ***")
Print("******************************")
Print()

its = E.getIterationNumber()
Print("Number of iterations of the method: %d" % its)

pep_type = E.getType()
Print("Solution method: %s" % pep_type)

nev, ncv, mpd = E.getDimensions()
Print("Number of requested eigenvalues: %d" % nev)

tol, maxit = E.getTolerances()
Print("Stopping condition: tol=%.4g, maxit=%d" % (tol, maxit))

nconv = E.getConverged()
Print("Number of converged eigenpairs %d" % nconv)

if nconv > 0:
    # Create the results vectors for individual solutions
    vr, wr = A0.getVecs()
    vi, wi = A0.getVecs()
    # bundle of all eigenvalues and eigenvectors
    eigval = np.zeros((1,nconv),dtype=complex)
    eigvec = np.zeros((nr,nconv),dtype=complex)
    #
    Print()
    Print("        k           relative error ")
    Print("----------------- -----------------")
    for i in range(nconv):
        k = E.getEigenpair(i, vr, vi)
        error = E.computeError(i)
        if k.imag != 0.0:
            Print(" %9f%+9fi %12g" % (k.real, k.imag, error))
        else:
            Print(" %12f      %12g" % (k.real, error))
    #    w = PETSc.Viewer().createASCII("test.txt")
    #    vr.view(w)
        tozero,VR = PETSc.Scatter.toZero(vr)
        tozero.begin(vr,VR)
        tozero.end(vr,VR)
        tozero.destroy()
        
        eigval[0,i] = k
        eigvec[0:,i] = VR[0:]
    Print()

# print to file
np.savetxt('eigenvalues.dat',np.hstack([np.real(eigval).transpose(),np.imag(eigval).transpose()]))
np.savetxt('Real_Eigenvec.dat',np.real(eigvec))
np.savetxt('Imag_Eigenvec.dat',np.imag(eigvec))
