
Processing file "heaps_msmax.ss"
Parsing heaps_msmax.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure ripple$int~int~int~int~node~node... 
Procedure ripple$int~int~int~int~node~node SUCCESS

Checking procedure deletemax$node... 
!!! REL :  DELM(mx,mx2,res)
!!! POST:  mx2>=0 & res>=mx2 & mx>=res
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [DELM]
              EBase exists (Expl)(Impl)[n; 
                    mx](ex)t::pq<n,mx>@M[Orig][LHSCase]@ rem br[{325}]&(
                    ([0!=n & 0<=n][0<=mx][null!=t]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 61::ref [t]
                                EXISTS(flted_206_53,
                                mx2: t'::pq<flted_206_53,mx2>@M[Orig][LHSCase]@ rem br[{326,325}]&
                                (
                                ([0<=flted_206_53 & 1+flted_206_53=n]
                                 [0<=mx2 & DELM(mx,mx2,res)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  mx](ex)t::pq<n,mx>@M[Orig][LHSCase]@ rem br[{325}]&(
                  ([1<=n][0<=mx][t!=null]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 61::ref [t]
                              EXISTS(flted_206_3353,
                              mx2_3354: t'::pq<flted_206_3353,mx2_3354>@M[Orig][LHSCase]@ rem br[{326,325}]&
                              (
                              ([res<=mx & 0<=mx & 0<=mx2_3354 & mx2_3354<=res]
                               [0<=flted_206_3353 & 0<=n & 1+flted_206_3353=n]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (mx2=0 & 0<=res & res<=mx) --> DELM(mx,mx2,res),
 (mx2=0 & 0<=res & res<=mx) --> DELM(mx,mx2,res),
 (0<=mx2 & mx2<=res & res<=mx) --> DELM(mx,mx2,res)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure deletemax$node SUCCESS

Checking procedure deleteone$int~int~node~node... 
Procedure deleteone$int~int~node~node SUCCESS

Checking procedure deleteoneel$node... 
Procedure deleteoneel$node SUCCESS

Checking procedure insert$node~int... 
Procedure insert$node~int SUCCESS

Termination checking result:

Stop Omega... 3227 invocations 
1 false contexts at: ( (156,2) )

Total verification time: 6.63 second(s)
	Time spent in main process: 2.07 second(s)
	Time spent in child processes: 4.56 second(s)
