
Processing file "heaps_ms.ss"
Parsing heaps_ms.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure deletemax$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ t!=null, t!=null, t!=null, t!=null, t!=null, t!=null, t!=null, t!=null, t!=null, t!=null, t!=null, t!=null, t!=null, t!=null, t!=null, t!=null, t!=null, t!=null, t!=null, t!=null, t!=null, t!=null, t!=null, t!=null]
!!! OLD SPECS: ((None,[]),EInfer [t]
              EBase exists (Expl)(Impl)[n](ex)t::pq2<n>@M[Orig][LHSCase]@ rem br[{325,324}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 61::ref [t]
                                EXISTS(n1: t'::pq2<n1>@M[Orig][LHSCase]@ rem br[{325,324}]&
                                (([0<=n1]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)t::pq2<n>@M[Orig][LHSCase]@ rem br[{325,324}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][t!=null]))&{FLOW,(1,23)=__flow}
                            EAssume 61::ref [t]
                              
                              EXISTS(n1_2137: true&(
                              ([t!=null][0<=res][null=t'][1=n & 0<=n]
                               [0=n1_2137]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(n1_2138: t'::pq2<n1_2138>@M[Orig][LHSCase]@ rem br[{325,324}]&
                                 (
                                 ([t'=t & t'!=null][0<=res][2=n & 0<=n]
                                  [1=n1_2138]))&
                                 {FLOW,(20,21)=__norm})
                              or EXISTS(n1_2139: t'::pq2<n1_2139>@M[Orig][LHSCase]@ rem br[{325,324}]&
                                 (
                                 ([1+n1_2139=n & 0<=n & 3<=n]
                                  [t'=t & t'!=null][0<=res]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[]
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
                              
                              EXISTS(m1_2194,
                              m2_2195: l'::pq2<m1_2194>@M[Orig][LHSCase]@ rem br[{325,324}] * 
                              r'::pq2<m2_2195>@M[Orig][LHSCase]@ rem br[{325,324}]&
                              (
                              ([l!=null]
                               [m2=m2' & m2=m1' & m2=m1_2194 & m2=m2_2195 & 
                                 -1+m1=m2_2195 & 0<=m2_2195]
                               [0<=res][r=r'][0<=m2_67][0<=m1_66]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(m1_2196,
                                 m2_2197: l'::pq2<m1_2196>@M[Orig][LHSCase]@ rem br[{325,324}] * 
                                 r'::pq2<m2_2197>@M[Orig][LHSCase]@ rem br[{325,324}]&
                                 (
                                 ([0<=res]
                                  [m2'=m2_2197 & -1+m1=m2' & -1+m1'=m2' & 
                                    0<=m2' & -1+m2=m2' & -1+m1_2196=m2']
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
                              
                              EXISTS(n1_2524: t'::pq2<n1_2524>@M[Orig][LHSCase]@ rem br[{325,324}]&
                              (
                              ([0<=res][t'=t & t'!=null][2=n & 0<=n]
                               [1=n1_2524]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(n1_2525: true&(
                                 ([t!=null][0<=res][null=t'][1=n & 0<=n]
                                  [0=n1_2525]))&
                                 {FLOW,(20,21)=__norm})
                              or EXISTS(n1_2526: t'::pq2<n1_2526>@M[Orig][LHSCase]@ rem br[{325,324}]&
                                 (
                                 ([1+n1_2526=n & 0<=n & 3<=n][0<=res]
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
!!! OLD SPECS: ((None,[]),EInfer [res,t,INS]
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
                              EXISTS(n1_2902: res::pq2<n1_2902>@M[Orig][LHSCase]@ rem br[{325,324}]&
                              (([0<=n1_2902 & 1+n=n1_2902 & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (n=0 & n1=1) --> INS(n1,n),
 (n1_2617=n_2603+1 & n1=(2*n_2603)+2 & n=(2*n_2603)+1 & 0<=n_2603 & 
  INS(n1_2617,n_2603)) --> INS(n1,n),
 (n1=(2*n1_2657)+1 & n=2*n1_2657 & n_2643=n1_2657-1 & 1<=n1_2657 & 
  INS(n1_2657,n_2643)) --> INS(n1,n),
 (n1_2719=n_2705+1 & n1=(2*n_2705)+2 & n=(2*n_2705)+1 & 0<=n_2705 & 
  INS(n1_2719,n_2705)) --> INS(n1,n),
 (n1=(2*n1_2755)+1 & n=2*n1_2755 & n_2741=n1_2755-1 & 1<=n1_2755 & 
  INS(n1_2755,n_2741)) --> INS(n1,n)]
!!! NEW ASSUME:[ RELASS [INS]: ( INS(n1_2617,n_2603)) -->  n1_2617=n_2603+1 | n1_2617<=n_2603 & n1_2617<=(0-1) | n_2603<=(n1_2617-2) & 
n_2603<=(0-1),
 RELASS [INS]: ( INS(n1_2657,n_2643)) -->  n1_2657=n_2643+1 | n1_2657<=n_2643 & n1_2657<=(0-1) | n_2643<=(n1_2657-2) & 
n_2643<=(0-1),
 RELASS [INS]: ( INS(n1_2719,n_2705)) -->  n1_2719=n_2705+1 | n1_2719<=n_2705 & n1_2719<=(0-1) | n_2705<=(n1_2719-2) & 
n_2705<=(0-1),
 RELASS [INS]: ( INS(n1_2755,n_2741)) -->  n1_2755=n_2741+1 | n1_2755<=n_2741 & n1_2755<=(0-1) | n_2741<=(n1_2755-2) & 
n_2741<=(0-1)]
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
                              EXISTS(m1_3491,
                              m2_3492: l::pq2<m1_3491>@M[Orig][LHSCase]@ rem br[{325,324}] * 
                              r::pq2<m2_3492>@M[Orig][LHSCase]@ rem br[{325,324}]&
                              (
                              ([0<=d][m2=m2_3492 & 0<=m2_3492]
                               [m1=m1_3491 & 0<=m1_3491][0<=m2_59][0<=m1_58]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (0<=d) --> RIP(d),
 (1<=d) --> RIP(d),
 (1<=d' & 0<=d & RIP(d')) --> RIP(d)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure ripple$int~int~int~int~node~node SUCCESS

Termination checking result:

Stop Omega... 2395 invocations 
0 false contexts at: ()

Total verification time: 2.14 second(s)
	Time spent in main process: 1.07 second(s)
	Time spent in child processes: 1.07 second(s)
