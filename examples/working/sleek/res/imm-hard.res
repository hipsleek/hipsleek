Starting Omega...oc

Entail (1) : Valid. 

 <1>(x::ll<n>@L[Orig][LHSCase]@ rem br[{1}] * y::ll<m>@L[Orig][LHSCase]@ rem br[{2}] ; true)&(([
                                                                    0!=n & 
                                                                    0<=n]
                                                                    [m=0]
                                                                    [null!=x]
                                                                    [null=y]))&{FLOW,(17,18)=__norm}[]


Entail (2) : Valid. 

 <1>x::ll<n>@L[Orig][LHSCase]@ rem br[{1}] * y::ll<m>@L[Orig][LHSCase]@ rem br[{1}]&(([
                                                                    n=n1 & 
                                                                    0<=n & 
                                                                    0!=n]
                                                                    [m=m1 & 
                                                                    0!=m & 
                                                                    0<=m]
                                                                    [null!=x]
                                                                    [null!=y]
                                                                    ))&{FLOW,(17,18)=__norm}[]


Entail (3) : Valid. 

 <1>(x::ll<n>@L[Orig][LHSCase]@ rem br[{1}] * y::ll<m>@L[Orig][LHSCase]@ rem br[{1}] ; true)&(([
                                                                    0<=n & 
                                                                    0!=n]
                                                                    [0!=m & 
                                                                    0<=m]
                                                                    [null!=x]
                                                                    [null!=y]
                                                                    ))&{FLOW,(17,18)=__norm}[]


Entail (4) : Valid. 

 <1>true&(([n=n1 & 0<=n & 0!=n][m=m1 & 0!=m & 0<=m][null!=x][null!=y]))&{FLOW,(17,18)=__norm}[]


Entail (5) : Valid. 

 <1>x::ll<n>@L[Orig][LHSCase]@ rem br[{1}] * y::ll<m>@L[Orig][LHSCase]@ rem br[{1}]&(([
                                                                    null!=x]
                                                                    [null!=y]
                                                                    [n=n1 & 
                                                                    0<=n & 
                                                                    0!=n]
                                                                    [m=m1 & 
                                                                    0<=m & 
                                                                    0!=m]))&{FLOW,(17,18)=__norm}[]


Entail (6) : Valid. 

 <1>(x::ll<n>@L[Orig][LHSCase]@ rem br[{1}] * y::ll<n>@L[Orig][LHSCase]@ rem br[{1}] ; true)&(([
                                                                    null!=y]
                                                                    [null!=x]
                                                                    [0<=n & 
                                                                    0!=n]))&{FLOW,(17,18)=__norm}[]


Entail (7) : Valid. 

 <1>false&(([false]))&{FLOW,(17,18)=__norm}[]


Entail (8) : Valid. 


Entail (9) : Valid. 


Entail (10) : Valid. 


Entail (11) : Valid. 

 <1>
    x::ll<n>@M[Orig][LHSCase]@ rem br[{1}] * 
    x::ll<n>@M[Orig][LHSCase]@ rem br[{1}]&(([0!=n & 0<=n][null!=x]))&
    {FLOW,(17,18)=__norm}[]
    or EXISTS(n_141: x::ll<n>@M[Orig][LHSCase]@ rem br[{2}] * 
       x::ll<n_141>@M[Orig][LHSCase]@ rem br[{2}]&(
       ([null=x][n=0 & n=n_141]))&{FLOW,(17,18)=__norm})[]
    

Stop Omega... 55 invocations 
