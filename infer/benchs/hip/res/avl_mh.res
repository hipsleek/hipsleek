
Processing file "avl_mh.ss"
Parsing avl_mh.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure build_avl1$node~node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ x!=null]
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase exists (Expl)(Impl)[nx1](ex)EXISTS(nx1_75: x::avl1<nx1>@M[Orig][LHSCase]@ rem br[{656,655}] * 
                    y::avl1<nx1_75>@M[Orig][LHSCase]@ rem br[{656,655}]&(
                    ([nx1=nx1_75 & 0<=nx1_75]))&{FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 47::
                                EXISTS(k: res::avl1<k>@M[Orig][LHSCase]@ rem br[{656,655}]&
                                (([0<=k]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[nx1](ex)x::avl1<nx1>@M[Orig][LHSCase]@ rem br[{656,655}] * 
                  y::avl1<nx1_75>@M[Orig][LHSCase]@ rem br[{656,655}]&(
                  ([nx1_75=nx1 & 0<=nx1_75]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][x!=null]))&{FLOW,(1,23)=__flow}
                            EAssume 47::
                              EXISTS(k_1660: res::avl1<k_1660>@M[Orig][LHSCase]@ rem br[{656,655}]&
                              (
                              ([-1+k_1660=nx1 & 0<=nx1 & 1<=nx1][res!=null]
                               [x!=null][0<=nx1_75]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure build_avl1$node~node SUCCESS

Checking procedure build_avl2$node~node~node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ y!=null]
!!! OLD SPECS: ((None,[]),EInfer [y]
              EBase exists (Expl)(Impl)[ny; Anon_12; Anon_13; Anon_14; 
                    Anon_15](ex)EXISTS(ny_73: y::avl1<ny>@M[Orig][LHSCase]@ rem br[{656,655}] * 
                    z::avl1<ny_73>@M[Orig][LHSCase]@ rem br[{656,655}] * 
                    x::node<Anon_12,Anon_13,Anon_14,Anon_15>@M[Orig][]&(
                    ([ny=ny_73 & 0<=ny_73][x!=null]))&{FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 51::ref [x]
                                EXISTS(k: x'::avl1<k>@M[Orig][LHSCase]@ rem br[{656,655}]&
                                (([0<=k]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[ny; Anon_12; Anon_13; Anon_14; 
                  Anon_15](ex)y::avl1<ny>@M[Orig][LHSCase]@ rem br[{656,655}] * 
                  z::avl1<ny_73>@M[Orig][LHSCase]@ rem br[{656,655}] * 
                  x::node<Anon_12,Anon_13,Anon_14,Anon_15>@M[Orig][]&(
                  ([ny_73=ny & 0<=ny_73][x!=null]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][y!=null]))&{FLOW,(1,23)=__flow}
                            EAssume 51::ref [x]
                              EXISTS(k_1753: x'::avl1<k_1753>@M[Orig][LHSCase]@ rem br[{656,655}]&
                              (
                              ([1+ny=k_1753 & 0<=ny & 2<=k_1753]
                               [x'=x & x'!=null][y!=null][0<=ny_73]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure build_avl2$node~node~node SUCCESS

Checking procedure get_max1$int~int... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase true&(())&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 19::
                                true&(())&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                    EAssume 19::
                      
                      true&(([res=a & b<=res]))&{FLOW,(20,21)=__norm}
                      or true&(([res=b & (1+a)<=res]))&{FLOW,(20,21)=__norm}
                      )
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure get_max1$int~int SUCCESS

Checking procedure height$node... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[h](ex)x::avl1<h>@M[Orig][LHSCase]@ rem br[{656,655}]&
                    (([0<=h]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 2::
                                EXISTS(h_112: x::avl1<h_112>@M[Orig][LHSCase]@ rem br[{656,655}]&
                                (([h=h_112 & 0<=h_112]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[h](ex)x::avl1<h>@M[Orig][LHSCase]@ rem br[{656,655}]&
                  (([0<=h]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 2::
                              
                              true&(([null=x][0=h & 0<=h][0=res]))&
                              {FLOW,(20,21)=__norm}
                              or EXISTS(h_1817: x::avl1<h_1817>@M[Orig][LHSCase]@ rem br[{656,655}]&
                                 (
                                 ([res=h & res=h_1817 & 1<=h_1817 & 0<=h]
                                  [x!=null]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure height$node SUCCESS

Checking procedure insert$node~int... 
!!! REL :  INS(k,n)
!!! POST:  0=n & 1=k
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [INS,x,a]
              EBase exists (Expl)(Impl)[n](ex)x::avl1<n>@M[Orig][LHSCase]@ rem br[{656,655}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 58::
                                EXISTS(k: res::avl1<k>@M[Orig][LHSCase]@ rem br[{656,655}]&
                                (([0<=k & INS(k,n)]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::avl1<n>@M[Orig][LHSCase]@ rem br[{656,655}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 58::
                              EXISTS(k_2556: res::avl1<k_2556>@M[Orig][LHSCase]@ rem br[{656,655}]&
                              (([1=k_2556 & 0<=k_2556][n=0 & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (n=0 & k=1) --> INS(k,n),
 (k=k_1880 & n_1866<n & k_1880<=(n+1) & (2*n)<=(1+n_1866+k_1880) & n<(n_1866+
  k_1880) & INS(k_1880,n_1866)) --> INS(k,n),
 (k=k_2203 & n_2189<n & k_2203<=(n+1) & n<(n_2189+k_2203) & (2*n)<=(1+n_2189+
  k_2203) & INS(k_2203,n_2189)) --> INS(k,n)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure insert$node~int SUCCESS

Checking procedure insert_inline$node~int... 
!!! OLD SPECS: ((None,[]),EInfer [x]
              EBase exists (Expl)(Impl)[n](ex)x::avl1<n>@M[Orig][LHSCase]@ rem br[{656,655}]&
                    (([0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 75::
                                EXISTS(n1: res::avl1<n1>@M[Orig][LHSCase]@ rem br[{656,655}]&
                                (([0<=n1 & (-1+n1)<=n & n<=n1]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n](ex)x::avl1<n>@M[Orig][LHSCase]@ rem br[{656,655}]&
                  (([0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 75::
                              
                              EXISTS(n1_3619: res::avl1<n1_3619>@M[Orig][LHSCase]@ rem br[{656,655}]&
                              (([res!=null][null=x][0=n & 0<=n][1=n1_3619]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(n1_3620: res::avl1<n1_3620>@M[Orig][LHSCase]@ rem br[{656,655}]&
                                 (
                                 ([n=n1_3620 & 2<=n & 0<=n][x!=null]
                                  [res!=null]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure insert_inline$node~int SUCCESS

Checking procedure merge$node~node... 
!!! REL :  MRG1(h2,h3)
!!! POST:  h2>=0 & h2=h3
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [MRG1,t1,t2]
              ECase case {
                     t1=null -> ((None,[]),EBase exists (Expl)(Impl)[h2](ex)
                                                 t2::avl1<h2>@M[Orig][LHSCase]@ rem br[{656,655}]&
                                                 (([0<=h2]))&
                                                 {FLOW,(20,21)=__norm}
                                                   EBase true&MayLoop&
                                                         {FLOW,(1,23)=__flow}
                                                           EAssume 158::
                                                             EXISTS(h3: 
                                                             res::avl1<h3>@M[Orig][LHSCase]@ rem br[{656,655}]&
                                                             (
                                                             ([0<=h3 & 
                                                                MRG1(h2,h3)]
                                                              ))&
                                                             {FLOW,(20,21)=__norm}))
                     ;
                     t1!=null -> ((None,[]),EBase exists (Expl)(Impl)[h1; 
                                                  h2](ex)t1::avl1<h1>@M[Orig][LHSCase]@ rem br[{656,655}] * 
                                                  t2::avl1<h2>@M[Orig][LHSCase]@ rem br[{656,655}]&
                                                  (([0<=h1][0<=h2]))&
                                                  {FLOW,(20,21)=__norm}
                                                    EBase true&MayLoop&
                                                          {FLOW,(1,23)=__flow}
                                                            EAssume 159::
                                                              EXISTS(Anon_17: 
                                                              res::avl1<Anon_17>@M[Orig][LHSCase]@ rem br[{656,655}]&
                                                              (
                                                              ([0<=Anon_17]))&
                                                              {FLOW,(20,21)=__norm}))
                     
                     })
!!! NEW SPECS: ((None,[]),ECase case {
                   t1=null -> ((None,[]),EBase exists (Expl)(Impl)[h2](ex)
                                               t2::avl1<h2>@M[Orig][LHSCase]@ rem br[{656,655}]&
                                               (([0<=h2]))&
                                               {FLOW,(20,21)=__norm}
                                                 EBase true&(([MayLoop]))&
                                                       {FLOW,(1,23)=__flow}
                                                         EAssume 158::
                                                           EXISTS(h3_3789: 
                                                           res::avl1<h3_3789>@M[Orig][LHSCase]@ rem br[{656,655}]&
                                                           (
                                                           ([h2=h3_3789 & 
                                                              0<=h2]
                                                            [null=t1]))&
                                                           {FLOW,(20,21)=__norm}))
                   ;
                   t1!=null -> ((None,[]),EBase exists (Expl)(Impl)[h1; 
                                                h2](ex)t1::avl1<h1>@M[Orig][LHSCase]@ rem br[{656,655}] * 
                                                t2::avl1<h2>@M[Orig][LHSCase]@ rem br[{656,655}]&
                                                (([0<=h1][0<=h2]))&
                                                {FLOW,(20,21)=__norm}
                                                  EBase true&(([MayLoop]))&
                                                        {FLOW,(1,23)=__flow}
                                                          EAssume 159::
                                                            EXISTS(Anon_3790: 
                                                            res::avl1<Anon_3790>@M[Orig][LHSCase]@ rem br[{656,655}]&
                                                            (
                                                            ([0<=Anon_3790]
                                                             [0<=h2][
                                                             0<=h1][t1!=null]
                                                             ))&
                                                            {FLOW,(20,21)=__norm}))
                   
                   })
!!! NEW RELS:[ (h3=h2 & 0<=h2) --> MRG1(h2,h3)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure merge$node~node SUCCESS

Checking procedure rotate_double_left$node~node~node~node~int~int~int... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[bn; cn; 
                    an](ex)EXISTS(an_83: a::avl1<an>@M[Orig][LHSCase]@ rem br[{656,655}] * 
                    b::avl1<bn>@M[Orig][LHSCase]@ rem br[{656,655}] * 
                    c::avl1<cn>@M[Orig][LHSCase]@ rem br[{656,655}] * 
                    d::avl1<an_83>@M[Orig][LHSCase]@ rem br[{656,655}]&(
                    ([an=an_83 & an=max(bn,cn) & 0<=bn & 0<=an & 0<=cn & (-1+
                       bn)<=cn & (-1+cn)<=bn]
                     ))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 22::
                                EXISTS(k: res::avl1<k>@M[Orig][LHSCase]@ rem br[{656,655}]&
                                (([0<=k]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[bn; cn; 
                  an](ex)a::avl1<an>@M[Orig][LHSCase]@ rem br[{656,655}] * 
                  b::avl1<bn>@M[Orig][LHSCase]@ rem br[{656,655}] * 
                  c::avl1<cn>@M[Orig][LHSCase]@ rem br[{656,655}] * 
                  d::avl1<an_83>@M[Orig][LHSCase]@ rem br[{656,655}]&(
                  ([an=an_83 & bn<=an & (2*an)<=(1+bn+cn) & cn<=an & an<=(bn+
                     cn)]
                   ))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 22::
                              EXISTS(k_3926: res::avl1<k_3926>@M[Orig][LHSCase]@ rem br[{656,655}]&
                              (
                              ([(bn=k_3926-2 & cn=k_3926-2 & an=k_3926-2 & 
                                 res!=null & 2<=k_3926 | bn=k_3926-3 & 
                                 cn=k_3926-2 & an=k_3926-2 & 3<=k_3926 & 
                                 res!=null | bn=k_3926-2 & cn=k_3926-3 & 
                                 an=k_3926-2 & res!=null & 3<=k_3926) & 
                                 0<=cn & 0<=an & 0<=bn]
                               [0<=an_83]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure rotate_double_left$node~node~node~node~int~int~int SUCCESS

Checking procedure rotate_double_right$node~node~node~node~int~int~int... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[bn; cn; 
                    an](ex)EXISTS(an_78: a::avl1<an>@M[Orig][LHSCase]@ rem br[{656,655}] * 
                    b::avl1<bn>@M[Orig][LHSCase]@ rem br[{656,655}] * 
                    c::avl1<cn>@M[Orig][LHSCase]@ rem br[{656,655}] * 
                    d::avl1<an_78>@M[Orig][LHSCase]@ rem br[{656,655}]&(
                    ([an=an_78 & an=max(bn,cn) & 0<=bn & 0<=an & 0<=cn & (-1+
                       cn)<=bn & (-1+bn)<=cn]
                     ))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 35::
                                EXISTS(k: res::avl1<k>@M[Orig][LHSCase]@ rem br[{656,655}]&
                                (([0<=k]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[bn; cn; 
                  an](ex)a::avl1<an>@M[Orig][LHSCase]@ rem br[{656,655}] * 
                  b::avl1<bn>@M[Orig][LHSCase]@ rem br[{656,655}] * 
                  c::avl1<cn>@M[Orig][LHSCase]@ rem br[{656,655}] * 
                  d::avl1<an_78>@M[Orig][LHSCase]@ rem br[{656,655}]&(
                  ([an=an_78 & bn<=an & (2*an)<=(1+bn+cn) & cn<=an & an<=(bn+
                     cn)]
                   ))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 35::
                              EXISTS(k_4062: res::avl1<k_4062>@M[Orig][LHSCase]@ rem br[{656,655}]&
                              (
                              ([(bn=k_4062-2 & cn=k_4062-2 & an=k_4062-2 & 
                                 res!=null & 2<=k_4062 | bn=k_4062-3 & 
                                 cn=k_4062-2 & an=k_4062-2 & 3<=k_4062 & 
                                 res!=null | bn=k_4062-2 & cn=k_4062-3 & 
                                 an=k_4062-2 & res!=null & 3<=k_4062) & 
                                 0<=cn & 0<=an & 0<=bn]
                               [0<=an_78]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure rotate_double_right$node~node~node~node~int~int~int SUCCESS

Checking procedure rotate_left$node~node~node... 
!!! OLD SPECS: ((None,[]),EInfer [rr]
              EBase exists (Expl)(Impl)[ln](ex)EXISTS(ln_103,
                    flted_41_102: l::avl1<ln>@M[Orig][LHSCase]@ rem br[{656,655}] * 
                    rl::avl1<ln_103>@M[Orig][LHSCase]@ rem br[{656,655}] * 
                    rr::avl1<flted_41_102>@M[Orig][LHSCase]@ rem br[{655}]&(
                    ([ln=ln_103 & 0<=ln & -1+flted_41_102=ln][null!=rr]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 5::
                                EXISTS(k: res::avl1<k>@M[Orig][LHSCase]@ rem br[{656,655}]&
                                (([0<=k]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[ln](ex)l::avl1<ln>@M[Orig][LHSCase]@ rem br[{656,655}] * 
                  rl::avl1<ln_103>@M[Orig][LHSCase]@ rem br[{656,655}] * 
                  rr::avl1<flted_41_102>@M[Orig][LHSCase]@ rem br[{655}]&(
                  ([1+ln=flted_41_102 & 1<=flted_41_102 & 1+
                     ln_103=flted_41_102]
                   [rr!=null]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 5::
                              EXISTS(k_4121: res::avl1<k_4121>@M[Orig][LHSCase]@ rem br[{656,655}]&
                              (
                              ([rr!=null][-2+k_4121=ln & 0<=ln][res!=null]
                               [0<=flted_41_102][0<=ln_103]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure rotate_left$node~node~node SUCCESS

Checking procedure rotate_right$node~node~node... 
!!! OLD SPECS: ((None,[]),EInfer [ll]
              EBase exists (Expl)(Impl)[lln](ex)EXISTS(flted_62_90,
                    flted_62_91: ll::avl1<lln>@M[Orig][LHSCase]@ rem br[{655}] * 
                    lr::avl1<flted_62_91>@M[Orig][LHSCase]@ rem br[{656,655}] * 
                    r::avl1<flted_62_90>@M[Orig][LHSCase]@ rem br[{656,655}]&
                    (
                    ([0<=flted_62_91 & 1+flted_62_90=lln & 1+flted_62_91=lln]
                     [null!=ll]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 12::
                                EXISTS(k: res::avl1<k>@M[Orig][LHSCase]@ rem br[{656,655}]&
                                (([0<=k]))&{FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[lln](ex)ll::avl1<lln>@M[Orig][LHSCase]@ rem br[{655}] * 
                  lr::avl1<flted_62_91>@M[Orig][LHSCase]@ rem br[{656,655}] * 
                  r::avl1<flted_62_90>@M[Orig][LHSCase]@ rem br[{656,655}]&(
                  ([flted_62_90=flted_62_91 & -1+lln=flted_62_90 & 
                     0<=flted_62_90]
                   [ll!=null]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 12::
                              EXISTS(k_4182: res::avl1<k_4182>@M[Orig][LHSCase]@ rem br[{656,655}]&
                              (
                              ([ll!=null][-1+k_4182=lln & 0<=lln & 1<=lln]
                               [res!=null][0<=flted_62_90][0<=flted_62_91]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure rotate_right$node~node~node SUCCESS

Termination checking result:

Stop Omega... 3197 invocations 
20 false contexts at: ( (493,17)  (493,24)  (497,3)  (497,22)  (497,10)  (496,15)  (496,27)  (496,8)  (495,14)  (495,26)  (495,8)  (495,3)  (376,12)  (372,20)  (316,14)  (312,20)  (235,14)  (231,22)  (214,12)  (210,20) )

Total verification time: 3.48 second(s)
	Time spent in main process: 1.98 second(s)
	Time spent in child processes: 1.5 second(s)
