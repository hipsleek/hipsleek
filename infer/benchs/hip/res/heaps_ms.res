
Processing file "heaps_ms.ss"
Parsing heaps_ms.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure deletemax$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ n!=0, n!=0, n!=0, n!=0, n!=0, n!=0, n!=0, n!=0, n!=0, n!=0, n!=0, n!=0, n!=0, n!=0, n!=0, n!=0, n!=0, n!=0, n!=0, n!=0, n!=0, n!=0, n!=0, n!=0]
!!! REL :  A(n1,n)
!!! POST:  n1>=0 & n1+1=n
!!! PRE :  1<=n
!!! OLD SPECS: ((None,[]),EInfer [n,A]
              EBase exists (Expl)(Impl)[n](ex)t::pq2<n>@M[Orig][LHSCase]@ rem br[{325,324}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 61::ref [t]
                                EXISTS(n1: t'::pq2<n1>@M[Orig][LHSCase]@ rem br[{325,324}]&
                                (([0<=n1 & A(n1,n)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)t::pq2<n>@M[Orig][LHSCase]@ rem br[{325,324}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][1<=n]))&{FLOW,(1,23)=__flow}
                            EAssume 61::ref [t]
                              EXISTS(n1_2115: t'::pq2<n1_2115>@M[Orig][LHSCase]@ rem br[{325,324}]&
                              (([1+n1_2115=n & 0<=n & 0<=n1_2115]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (n1=0 & n=1) --> A(n1,n),
 (n1=1 & n=2) --> A(n1,n),
 (n1=n-1 & 3<=n) --> A(n1,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure deletemax$node SUCCESS

Checking procedure deleteone$int~int~node~node... 
!!! OLD SPECS: ((None,[]),EInfer [l,r]
              EBase EXISTS(m1_66,
                    m2_67: l::pq2<m1_66>@M[Orig][LHSCase]@ rem br[{324}] * 
                    r::pq2<m2_67>@M[Orig][LHSCase]@ rem br[{325,324}]&(
                    ([m1=m1_66 & m2=m2_67 & 0!=m1_66 & 0<=m1_66 & (-1+
                       m1)<=m2 & m2<=m1]
                     [null!=l]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 38::ref [m1;m2;l;r]
                                EXISTS(m1_68,
                                m2_69: l'::pq2<m1_68>@M[Orig][LHSCase]@ rem br[{325,324}] * 
                                r'::pq2<m2_69>@M[Orig][LHSCase]@ rem br[{325,324}]&
                                (
                                ([m1'=m1_68 & 0<=m1_68][m2'=m2_69 & 0<=m2_69]
                                 ))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase l::pq2<m1_66>@M[Orig][LHSCase]@ rem br[{324}] * 
                  r::pq2<m2_67>@M[Orig][LHSCase]@ rem br[{325,324}]&(
                  ([l!=null]
                   [m2=m2_67 & m1=m1_66 & m2<=m1 & (-1+m1)<=m2 & 1<=m1]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 38::ref [m1;m2;l;r]
                              
                              EXISTS(m1_2170,
                              m2_2171: l'::pq2<m1_2170>@M[Orig][LHSCase]@ rem br[{325,324}] * 
                              r'::pq2<m2_2171>@M[Orig][LHSCase]@ rem br[{325,324}]&
                              (
                              ([l!=null]
                               [m2=m2' & m2=m1' & m2=m1_2170 & m2=m2_2171 & 
                                 -1+m1=m2_2171 & 0<=m2_2171]
                               [0<=res][r=r'][0<=m2_67][0<=m1_66]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(m1_2172,
                                 m2_2173: l'::pq2<m1_2172>@M[Orig][LHSCase]@ rem br[{325,324}] * 
                                 r'::pq2<m2_2173>@M[Orig][LHSCase]@ rem br[{325,324}]&
                                 (
                                 ([0<=res]
                                  [m2'=m2_2173 & -1+m1=m2' & -1+m1'=m2' & 
                                    0<=m2' & -1+m2=m2' & -1+m1_2172=m2']
                                  [r!=null][l=l' & l!=null][0<=m2_67]
                                  [0<=m1_66]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure deleteone$int~int~node~node SUCCESS

Checking procedure deleteoneel$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ t!=null, t!=null, t!=null, t!=null, t!=null, t!=null]
!!! OLD SPECS: ((None,[]),EInfer [t]
              EBase exists (Expl)(Impl)[n](ex)t::pq2<n>@M[Orig][LHSCase]@ rem br[{325,324}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 30::ref [t]
                                EXISTS(n1: t'::pq2<n1>@M[Orig][LHSCase]@ rem br[{325,324}]&
                                (([0<=n1]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)t::pq2<n>@M[Orig][LHSCase]@ rem br[{325,324}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][t!=null]))&{FLOW,(1,23)=__flow}
                            EAssume 30::ref [t]
                              
                              EXISTS(n1_2500: t'::pq2<n1_2500>@M[Orig][LHSCase]@ rem br[{325,324}]&
                              (
                              ([0<=res][t'=t & t'!=null][2=n & 0<=n]
                               [1=n1_2500]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(n1_2501: true&(
                                 ([t!=null][0<=res][null=t'][1=n & 0<=n]
                                  [0=n1_2501]))&
                                 {FLOW,(20,21)=__norm})
                              or EXISTS(n1_2502: t'::pq2<n1_2502>@M[Orig][LHSCase]@ rem br[{325,324}]&
                                 (
                                 ([1+n1_2502=n & 0<=n & 3<=n][0<=res]
                                  [t'=t & t'!=null]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure deleteoneel$node SUCCESS

Checking procedure insert$node~int... 
!!! REL :  INS(n1,n)
!!! POST:  n>=0 & n+1=n1
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [t,INS]
              EBase exists (Expl)(Impl)[n](ex)t::pq2<n>@M[Orig][LHSCase]@ rem br[{325,324}]&
                    (([0<=v][0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 1::
                                EXISTS(n1: res::pq2<n1>@M[Orig][LHSCase]@ rem br[{325,324}]&
                                (([0<=n1 & INS(n1,n)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)t::pq2<n>@M[Orig][LHSCase]@ rem br[{325,324}]&
                  (([0<=v][0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 1::
                              EXISTS(n1_2878: res::pq2<n1_2878>@M[Orig][LHSCase]@ rem br[{325,324}]&
                              (([0<=n1_2878 & 1+n=n1_2878 & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (n=0 & n1=1) --> INS(n1,n),
 (n1_2593=n_2579+1 & n1=(2*n_2579)+2 & n=(2*n_2579)+1 & 0<=n_2579 & 
  INS(n1_2593,n_2579)) --> INS(n1,n),
 (n1=(2*n1_2633)+1 & n=2*n1_2633 & n_2619=n1_2633-1 & 1<=n1_2633 & 
  INS(n1_2633,n_2619)) --> INS(n1,n),
 (n1_2695=n_2681+1 & n1=(2*n_2681)+2 & n=(2*n_2681)+1 & 0<=n_2681 & 
  INS(n1_2695,n_2681)) --> INS(n1,n),
 (n1=(2*n1_2731)+1 & n=2*n1_2731 & n_2717=n1_2731-1 & 1<=n1_2731 & 
  INS(n1_2731,n_2717)) --> INS(n1,n)]
!!! NEW ASSUME:[ RELASS [INS]: ( INS(n1_2593,n_2579)) -->  n1_2593=n_2579+1 | n1_2593<=n_2579 & n1_2593<=(0-1) | n_2579<=(n1_2593-2) & 
n_2579<=(0-1),
 RELASS [INS]: ( INS(n1_2633,n_2619)) -->  n1_2633=n_2619+1 | n1_2633<=n_2619 & n1_2633<=(0-1) | n_2619<=(n1_2633-2) & 
n_2619<=(0-1),
 RELASS [INS]: ( INS(n1_2695,n_2681)) -->  n1_2695=n_2681+1 | n1_2695<=n_2681 & n1_2695<=(0-1) | n_2681<=(n1_2695-2) & 
n_2681<=(0-1),
 RELASS [INS]: ( INS(n1_2731,n_2717)) -->  n1_2731=n_2717+1 | n1_2731<=n_2717 & n1_2731<=(0-1) | n_2717<=(n1_2731-2) & 
n_2717<=(0-1)]
!!! NEW RANK:[]
Procedure insert$node~int SUCCESS

Checking procedure ripple$int~int~int~int~node~node... 
!!! REL :  RIP(d)
!!! POST:  d>=0
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [RIP,m1,m2]
              EBase EXISTS(m1_58,
                    m2_59: l::pq2<m1_58>@M[Orig][LHSCase]@ rem br[{325,324}] * 
                    r::pq2<m2_59>@M[Orig][LHSCase]@ rem br[{325,324}]&(
                    ([v<=d & 0<=v][m1=m1_58 & 0<=m1_58][m2=m2_59 & 0<=m2_59]))&
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
                  ([m1_58=m1 & 0<=m1_58][m2_59=m2 & 0<=m2_59][0<=v & v<=d]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 45::ref [d]
                              EXISTS(m1_3467,
                              m2_3468: l::pq2<m1_3467>@M[Orig][LHSCase]@ rem br[{325,324}] * 
                              r::pq2<m2_3468>@M[Orig][LHSCase]@ rem br[{325,324}]&
                              (
                              ([0<=d][m2=m2_3468 & 0<=m2_3468]
                               [m1=m1_3467 & 0<=m1_3467][0<=m2_59][0<=m1_58]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (0<=d) --> RIP(d),
 (1<=d) --> RIP(d),
 (1<=d' & 0<=d & RIP(d')) --> RIP(d)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure ripple$int~int~int~int~node~node SUCCESS

Termination checking result:

Stop Omega... 2506 invocations 
0 false contexts at: ()

Total verification time: 2.25 second(s)
	Time spent in main process: 1. second(s)
	Time spent in child processes: 1.25 second(s)
