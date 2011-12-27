
Processing file "r1a-i.ss"
Parsing r1a-i.ss ...
Parsing ../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure length$node... OLD SPECS:  EInfer [R]
   EBase exists (Expl)(Impl)[n](ex)x::ll<n>@L[Orig][LHSCase] & true &
         {FLOW,(20,21)=__norm}
           EAssume 1::
             true & R(res,n) & {FLOW,(20,21)=__norm}
NEW SPECS:  EBase exists (Expl)(Impl)[n](ex)x::ll<n>@L[Orig][LHSCase] & true &
       {FLOW,(20,21)=__norm}
         EAssume 1::
           
           true &
           exists(v_int_18_501':exists(v_bool_18_507':exists(R:x=null & 
           v_bool_18_507' & x=null & v_bool_18_507' & v_int_18_501'=0 & 
           res=v_int_18_501' & R(res,n)))) & 0<=n & {FLOW,(20,21)=__norm}
           or true &
              exists(v_bool_18_507':exists(flted_7_534:exists(R:exists(n_539:exists(r_24':exists(v_int_21_506':flted_7_534+
              1=n & x!=null & 129::!(v_bool_18_507') & x!=null & 
              !(v_bool_18_507') & n_539=flted_7_534 & R(r_24',n_539) & 
              0<=n_539 & v_int_21_506'=r_24'+1 & res=v_int_21_506' & 
              R(res,n))))))) & 0<=n & {FLOW,(20,21)=__norm}
           
NEW RELS: [ ( v_int_18_501'=0 & n=0 & res=v_int_18_501') -->  R(res,n), ( (flted_7_534=0 | 1<=flted_7_534) & res=v_int_21_506' & R(r_24',n_539) & 
flted_7_534+1=n & n_539=flted_7_534 & 0<=n_539 & v_int_21_506'=r_24'+1) -->  R(res,n)]

Procedure length$node SUCCESS
Stop Omega... 63 invocations 
0 false contexts at: ()

Total verification time: 0.368022 second(s)
	Time spent in main process: 0.32402 second(s)
	Time spent in child processes: 0.044002 second(s)
