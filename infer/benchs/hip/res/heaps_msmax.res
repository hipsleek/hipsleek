
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
                    mx](ex)t::pq<n,mx>@M[Orig][LHSCase]@ rem br[{327}]&(
                    ([0!=n & 0<=n][0<=mx][null!=t]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 61::ref [t]
                                EXISTS(flted_203_56,
                                mx2: t'::pq<flted_203_56,mx2>@M[Orig][LHSCase]@ rem br[{328,327}]&
                                (
                                ([0<=flted_203_56 & 1+flted_203_56=n]
                                 [0<=mx2 & DELM(mx,mx2,res)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  mx](ex)t::pq<n,mx>@M[Orig][LHSCase]@ rem br[{327}]&(
                  ([1<=n][0<=mx][t!=null]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 61::ref [t]
                              EXISTS(flted_203_3392,
                              mx2_3393: t'::pq<flted_203_3392,mx2_3393>@M[Orig][LHSCase]@ rem br[{328,327}]&
                              (
                              ([res<=mx & 0<=mx & 0<=mx2_3393 & mx2_3393<=res]
                               [0<=flted_203_3392 & 0<=n & 1+flted_203_3392=n]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (mx2=0 & 0<=res & res<=mx) --> DELM(mx,mx2,res),
 (mx2=0 & 0<=res & res<=mx) --> DELM(mx,mx2,res),
 (0<=mx2 & mx2<=res & res<=mx) --> DELM(mx,mx2,res)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure deletemax$node SUCCESS

Checking procedure deleteone$int~int~node~node... 
!!! REL :  DELONE(mx3,mx1,mx2,mx4)
!!! POST:  mx3>=0 & mx1>=mx3 & mx4>=0 & mx2>=mx4
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [DELONE]
              EBase exists (Expl)(Impl)[mx1; mx2](ex)EXISTS(m1_68,
                    m2_69: l::pq<m1_68,mx1>@M[Orig][LHSCase]@ rem br[{327}] * 
                    r::pq<m2_69,mx2>@M[Orig][LHSCase]@ rem br[{328,327}]&(
                    ([m1=m1_68 & m2=m2_69 & 0!=m1_68 & 0<=m1_68 & (-1+
                       m1)<=m2 & m2<=m1]
                     [0<=mx1][null!=l][0<=mx2]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 39::ref [m1;m2;l;r]
                                EXISTS(m1_70,m2_71,n3,n4,maxi,mx3,
                                mx4: l'::pq<m1_70,mx3>@M[Orig][LHSCase]@ rem br[{328,327}] * 
                                r'::pq<m2_71,mx4>@M[Orig][LHSCase]@ rem br[{328,327}]&
                                (
                                ([maxi=max(mx1,mx2) & 0<=mx3 & 0<=mx4 & 
                                   DELONE(mx3,mx1,mx2,mx4) & res<=maxi & 
                                   0<=res]
                                 [m1'=m1_70 & m1'=n3 & m2'=m2_71 & m2'=n4 & 
                                   0<=m2_71 & (-1+m1')<=m2' & m2'<=m1' & m1'+
                                   m2'=-1+m1+m2]
                                 ))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[mx1; 
                  mx2](ex)l::pq<m1_68,mx1>@M[Orig][LHSCase]@ rem br[{327}] * 
                  r::pq<m2_69,mx2>@M[Orig][LHSCase]@ rem br[{328,327}]&(
                  ([0<=mx1][l!=null][0<=mx2]
                   [m2=m2_69 & m1=m1_68 & m2<=m1 & (-1+m1)<=m2 & 1<=m1]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 39::ref [m1;m2;l;r]
                              EXISTS(m1_3468,m2_3469,n3_3470,n4_3471,
                              maxi_3472,mx3_3473,
                              mx4_3474: l'::pq<m1_3468,mx3_3473>@M[Orig][LHSCase]@ rem br[{328,327}] * 
                              r'::pq<m2_3469,mx4_3474>@M[Orig][LHSCase]@ rem br[{328,327}]&
                              (
                              ([maxi_3472=max(mx1,mx2) & res<=maxi_3472 & 
                                 0<=mx1 & mx4_3474<=mx2 & 0<=mx2 & 0<=res & 
                                 mx3_3473<=mx1 & 0<=mx4_3474 & 0<=mx3_3473]
                               [m2'=m2_3469 & m2'=n4_3471 & m1'=m1_3468 & 
                                 m1'=n3_3470 & 0<=m2_3469 & m2'<=m1' & m1'+
                                 m2'=-1+m1+m2 & (-1+m1')<=m2']
                               [0<=m2_69][0<=m1_68]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (mx4=mx2 & 0<=mx3 & mx3<=mx1 & 0<=mx2) --> DELONE(mx3,mx1,mx2,mx4),
 (mx3=mx1 & 0<=mx4 & mx4<=mx2 & 0<=mx1) --> DELONE(mx3,mx1,mx2,mx4)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure deleteone$int~int~node~node SUCCESS

Checking procedure deleteoneel$node... 
!!! REL :  DEL(res,mx,mx2)
!!! POST:  res>=0 & mx>=res & mx2>=0 & mx>=mx2
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [DEL]
              EBase exists (Expl)(Impl)[n; 
                    mx](ex)t::pq<n,mx>@M[Orig][LHSCase]@ rem br[{327}]&(
                    ([0!=n & 0<=n][0<=mx][null!=t]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 31::ref [t]
                                EXISTS(flted_89_77,
                                mx2: t'::pq<flted_89_77,mx2>@M[Orig][LHSCase]@ rem br[{328,327}]&
                                (
                                ([0<=flted_89_77 & 1+flted_89_77=n]
                                 [0<=mx2 & DEL(res,mx,mx2)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  mx](ex)t::pq<n,mx>@M[Orig][LHSCase]@ rem br[{327}]&(
                  ([1<=n][0<=mx][t!=null]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 31::ref [t]
                              EXISTS(flted_89_3866,
                              mx2_3867: t'::pq<flted_89_3866,mx2_3867>@M[Orig][LHSCase]@ rem br[{328,327}]&
                              (
                              ([0<=res & 0<=mx & mx2_3867<=mx & 
                                 0<=mx2_3867 & res<=mx]
                               [0<=flted_89_3866 & 0<=n & 1+flted_89_3866=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (mx2=0 & 0<=res & res<=mx) --> DEL(res,mx,mx2),
 (res=0 & mx2=0 & 0<=mx) --> DEL(res,mx,mx2),
 (0<=res & res<=mx2 & mx2<=mx) --> DEL(res,mx,mx2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure deleteoneel$node SUCCESS

Checking procedure insert$node~int... 
Procedure insert$node~int SUCCESS

Termination checking result:

Stop Omega... 3297 invocations 
1 false contexts at: ( (153,2) )

Total verification time: 7.54 second(s)
	Time spent in main process: 2.1 second(s)
	Time spent in child processes: 5.44 second(s)
