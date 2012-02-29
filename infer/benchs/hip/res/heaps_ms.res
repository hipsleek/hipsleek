
Processing file "heaps_ms.ss"
Parsing heaps_ms.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure deletemax$node... 
Procedure deletemax$node SUCCESS

Checking procedure deleteone$int~int~node~node... 
Procedure deleteone$int~int~node~node SUCCESS

Checking procedure deleteoneel$node... 
Procedure deleteoneel$node SUCCESS

Checking procedure insert$node~int... 
!!! OLD SPECS: ((None,[]),EInfer [INS]
              EBase exists (Expl)(Impl)[n](ex)t::pq2<n>@M[Orig][LHSCase]@ rem br[{325,324}]&
                    (([0<=v][0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 1::
                                EXISTS(n1: res::pq2<n1>@M[Orig][LHSCase]@ rem br[{325,324}]&
                                (([0<=n1 & -1+n1=n]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)t::pq2<n>@M[Orig][LHSCase]@ rem br[{325,324}]&
                  (([0<=v][0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 1::
                              
                              EXISTS(n1_2849: res::pq2<n1_2849>@M[Orig][LHSCase]@ rem br[{325,324}]&
                              (
                              ([0<=v][res!=null][null=t][1=n1_2849]
                               [0=n & 0<=n]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(n1_2850: res::pq2<n1_2850>@M[Orig][LHSCase]@ rem br[{325,324}]&
                                 (
                                 ([res=t & exists(alpha:2*alpha=1+n & 
                                    res!=null & 0<=v & 1<=n) & -1+
                                    n1_2850=n & 0<=n]
                                  ))&
                                 {FLOW,(20,21)=__norm})
                              or EXISTS(n1_2851: res::pq2<n1_2851>@M[Orig][LHSCase]@ rem br[{325,324}]&
                                 (
                                 ([res=t & exists(alpha:2*alpha=2+n & 
                                    res!=null & 0<=v & 2<=n) & -1+
                                    n1_2851=n & 0<=n]
                                  ))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure insert$node~int SUCCESS

Checking procedure ripple$int~int~int~int~node~node... 
!!! REL :  RIP(d)
!!! POST:  d>=0
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [RIP]
              EBase EXISTS(m1_58,
                    m2_59: l::pq2<m1_58>@M[Orig][LHSCase]@ rem br[{325,324}] * 
                    r::pq2<m2_59>@M[Orig][LHSCase]@ rem br[{325,324}]&(
                    ([v<=d & 0<=v]
                     [m1=m1_58 & m2=m2_59 & 0<=m2_59 & (-1+m1)<=m2 & m2<=m1]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 45::ref [d]
                                EXISTS(m1_60,
                                m2_61: l::pq2<m1_60>@M[Orig][LHSCase]@ rem br[{325,324}] * 
                                r::pq2<m2_61>@M[Orig][LHSCase]@ rem br[{325,324}]&
                                (
                                ([RIP(d)][m1=m1_60 & 0<=m1_60]
                                 [m2=m2_61 & 0<=m2_61]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase l::pq2<m1_58>@M[Orig][LHSCase]@ rem br[{325,324}] * 
                  r::pq2<m2_59>@M[Orig][LHSCase]@ rem br[{325,324}]&(
                  ([0<=v & v<=d]
                   [m1=m1_58 & m2=m2_59 & 0<=m2 & m2<=m1 & (-1+m1)<=m2]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 45::ref [d]
                              EXISTS(m1_3447,
                              m2_3448: l::pq2<m1_3447>@M[Orig][LHSCase]@ rem br[{325,324}] * 
                              r::pq2<m2_3448>@M[Orig][LHSCase]@ rem br[{325,324}]&
                              (
                              ([0<=d][m2=m2_3448 & 0<=m2_3448]
                               [m1=m1_3447 & 0<=m1_3447][0<=m2_59][0<=m1_58]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(d_2914:exists(v:v<=d & 0<=d_2914 & d_2914<=v))) --> RIP(d),
 (exists(v:exists(d_2914:0<=v & v<=d & (1+v)<=d_2914))) --> RIP(d),
 (exists(v:exists(d_2914:0<=v & v<=d & (1+v)<=d_2914))) --> RIP(d),
 (exists(v:exists(d_2914:0<=v & v<=d & (1+v)<=d_2914))) --> RIP(d),
 (exists(v:exists(d_2914:0<=v & v<=d & (1+v)<=d_2914))) --> RIP(d),
 (exists(v:exists(d_2914:0<=v & v<=d & (1+v)<=d_2914))) --> RIP(d),
 (exists(v:0<=v & v<=d)) --> RIP(d),
 (exists(d_2914:exists(v:v<=d & 0<=d_2914 & d_2914<=v))) --> RIP(d),
 (exists(v:exists(d_2914:0<=v & v<=d & (1+v)<=d_2914))) --> RIP(d),
 (exists(d_3020:exists(d_2974:0<=d_3020 & exists(d':d_3020<=d_2974 & 
  d_2974<=d' & d'<=d)))) --> RIP(d),
 (exists(d_3020:RIP(d') & exists(d_2974:0<=d_3020 & 
  exists(v:d_3020<=d_2974 & (1+v)<=d_2974 & 0<=v & d'=d_2974 & 
  v<=d)))) --> RIP(d),
 (exists(d_2974:exists(d_3020:0<=d_2974 & exists(d':(1+d_2974)<=d_3020 & 
  d_3020<=d' & d'<=d)))) --> RIP(d),
 (exists(d_2974:RIP(d') & 0<=d_2974 & (1+d_2974)<=d' & exists(v:0<=v & (1+
  v)<=d' & v<=d))) --> RIP(d)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure ripple$int~int~int~int~node~node SUCCESS

Termination checking result:

Stop Omega... 1947 invocations 
1 false contexts at: ( (145,2) )

Total verification time: 1.54 second(s)
	Time spent in main process: 0.95 second(s)
	Time spent in child processes: 0.59 second(s)
