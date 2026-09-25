# validate the CEGAR machinery on N=10 against the known direct results
import base_cegar as C
print("rho=3 f=6 N=10 (expect HOLDS)"); C.run(3,6,(None,None,None),N=10)
print("rho=3 f=5 N=10 no caps (expect COUNTEREXAMPLE)"); C.run(3,5,(None,None,None),N=10)
print("rho=3 f=5 N=10 caps lines<=4 planes<=6 (expect HOLDS)"); C.run(3,5,(None,4,6),N=10)
