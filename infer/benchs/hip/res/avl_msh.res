
Processing file "avl_msh.ss"
Parsing avl_msh.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure build_avl1$node~node... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[mx; my; 
                    nx1](ex)EXISTS(nx1_88: x::avl<mx,nx1>@M[Orig][LHSCase]@ rem br[{655}] * 
                    y::avl<my,nx1_88>@M[Orig][LHSCase]@ rem br[{655}]&(
                    ([null!=x][nx1=nx1_88 & 0!=nx1_88 & 0<=nx1]
                     [0<=mx & 0!=mx][0<=my & 0!=my][null!=y]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 47::
                                EXISTS(flted_162_87,k,
                                nx: res::avl<k,flted_162_87>@M[Orig][LHSCase]@ rem br[{656,655}]&
                                (
                                ([0<=flted_162_87 & -1+flted_162_87=nx][
                                 0<=k]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[mx; my; 
                  nx1](ex)x::avl<mx,nx1>@M[Orig][LHSCase]@ rem br[{655}] * 
                  y::avl<my,nx1_88>@M[Orig][LHSCase]@ rem br[{655}]&(
                  ([x!=null][nx1=nx1_88 & 1<=nx1][1<=mx][1<=my][y!=null]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 47::
                              EXISTS(nx_1839: res::avl<k,flted_162_87>@M[Orig][LHSCase]@ rem br[{656,655}]&
                              (
                              ([y!=null][res!=null]
                               [nx1=nx_1839 & -1+flted_162_87=nx1 & 0<=nx1 & 
                                 1<=nx1]
                               [x!=null]
                               [k=1+mx+my & 0<=mx & 1<=mx & 0<=my & 1<=my]
                               [0<=nx1_88]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure build_avl1$node~node SUCCESS

Checking procedure build_avl2$node~node~node... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[my; mz; ny; Anon_12; Anon_13; 
                    Anon_14; 
                    Anon_15](ex)EXISTS(ny_84: y::avl<my,ny>@M[Orig][LHSCase]@ rem br[{655}] * 
                    z::avl<mz,ny_84>@M[Orig][LHSCase]@ rem br[{655}] * 
                    x::node<Anon_12,Anon_13,Anon_14,Anon_15>@M[Orig][]&(
                    ([null!=y][ny=ny_84 & 0!=ny_84 & 0<=ny][0<=my & 0!=my]
                     [0<=mz & 0!=mz][null!=z][x!=null]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 51::ref [x]
                                EXISTS(flted_178_83,
                                k: x'::avl<k,flted_178_83>@M[Orig][LHSCase]@ rem br[{656,655}]&
                                (
                                ([0<=flted_178_83 & -1+flted_178_83=ny][
                                 0<=k]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[my; mz; ny; Anon_12; Anon_13; Anon_14; 
                  Anon_15](ex)y::avl<my,ny>@M[Orig][LHSCase]@ rem br[{655}] * 
                  z::avl<mz,ny_84>@M[Orig][LHSCase]@ rem br[{655}] * 
                  x::node<Anon_12,Anon_13,Anon_14,Anon_15>@M[Orig][]&(
                  ([y!=null][ny=ny_84 & 1<=ny][1<=my][1<=mz][z!=null]
                   [x!=null]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 51::ref [x]
                              EXISTS(k_1954,
                              flted_178_1955: x'::avl<k_1954,flted_178_1955>@M[Orig][LHSCase]@ rem br[{656,655}]&
                              (
                              ([1+ny=flted_178_1955 & 0<=ny & 
                                 2<=flted_178_1955]
                               [x'=x & x'!=null][z!=null][y!=null]
                               [k_1954=1+my+mz & 0<=my & 1<=mz & 0<=mz & 
                                 1<=my]
                               [0<=ny_84]))&
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

Checking procedure height1$node... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[m; 
                    n](ex)x::avl<m,n>@M[Orig][LHSCase]@ rem br[{656,655}]&(
                    ([0<=m][0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 1::
                                EXISTS(m_147,
                                n_148: x::avl<m_147,n_148>@M[Orig][LHSCase]@ rem br[{656,655}]&
                                (([m=m_147 & 0<=m_147][n=n_148 & 0<=n_148]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[m; 
                  n](ex)x::avl<m,n>@M[Orig][LHSCase]@ rem br[{656,655}]&(
                  ([0<=m][0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 1::
                              
                              true&(
                              ([null=x][0=n & 0<=n][0=m & 0<=m][0=res]))&
                              {FLOW,(20,21)=__norm}
                              or EXISTS(m_2035,
                                 n_2036: x::avl<m_2035,n_2036>@M[Orig][LHSCase]@ rem br[{656,655}]&
                                 (
                                 ([m=m_2035 & 1<=m & 0<=m]
                                  [res=n & res=n_2036 & 1<=n_2036 & 0<=n]
                                  [x!=null]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure height1$node SUCCESS

Checking procedure insert$node~int... 
!!! REL :  INS(k,m)
!!! POST:  0=m & 1=k
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [INS]
              EBase exists (Expl)(Impl)[m; 
                    n](ex)x::avl<m,n>@M[Orig][LHSCase]@ rem br[{656,655}]&(
                    ([0<=m][0<=n]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 58::
                                EXISTS(Anon_17,
                                k: res::avl<k,Anon_17>@M[Orig][LHSCase]@ rem br[{656,655}]&
                                (([0<=k & INS(k,m)][0<=Anon_17]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[m; 
                  n](ex)x::avl<m,n>@M[Orig][LHSCase]@ rem br[{656,655}]&(
                  ([0<=m][0<=n]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 58::
                              EXISTS(Anon_2921,
                              k_2922: res::avl<k_2922,Anon_2921>@M[Orig][LHSCase]@ rem br[{656,655}]&
                              (
                              ([1=k_2922 & 0<=k_2922][m=0 & 0<=m]
                               [0<=Anon_2921][0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (m=0 & k=1) --> INS(k,m),
 (m_2094=(m+k_2115)-k & 2<=k_2115 & k_2115<k & k<=(m+k_2115) & 
  INS(k_2115,m_2094)) --> INS(k,m),
 (m_2094=(m-k)+k_2115 & 2<=k_2115 & k_2115<k & k<=(m+k_2115) & 
  INS(k_2115,m_2094)) --> INS(k,m),
 (m_2478=(m+k_2499)-k & 2<=k_2499 & k_2499<k & k<=(m+k_2499) & 
  INS(k_2499,m_2478)) --> INS(k,m)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure insert$node~int SUCCESS

Checking procedure insert_inline$node~int... 
Procedure insert_inline$node~int SUCCESS

Checking procedure merge$node~node... 
!!! REL :  MRG2(s3,s2)
!!! POST:  s2>=0 & s2=s3
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [MRG2]
              ECase case {
                     t1=null -> ((None,[]),EBase exists (Expl)(Impl)[s2; 
                                                 h2](ex)t2::avl<s2,h2>@M[Orig][LHSCase]@ rem br[{656,655}]&
                                                 (([0<=s2][0<=h2]))&
                                                 {FLOW,(20,21)=__norm}
                                                   EBase true&MayLoop&
                                                         {FLOW,(1,23)=__flow}
                                                           EAssume 158::
                                                             EXISTS(h2_65,
                                                             s3: res::avl<s3,h2_65>@M[Orig][LHSCase]@ rem br[{656,655}]&
                                                             (
                                                             ([0<=s3 & 
                                                                MRG2(s3,s2)]
                                                              [h2=h2_65 & 
                                                                0<=h2_65]
                                                              ))&
                                                             {FLOW,(20,21)=__norm}))
                     ;
                     t1!=null -> ((None,[]),EBase exists (Expl)(Impl)[s1; 
                                                  h1; s2; 
                                                  h2](ex)t1::avl<s1,h1>@M[Orig][LHSCase]@ rem br[{656,655}] * 
                                                  t2::avl<s2,h2>@M[Orig][LHSCase]@ rem br[{656,655}]&
                                                  (
                                                  ([0<=s1][0<=h1][0<=s2]
                                                   [0<=h2]))&
                                                  {FLOW,(20,21)=__norm}
                                                    EBase true&MayLoop&
                                                          {FLOW,(1,23)=__flow}
                                                            EAssume 159::
                                                              EXISTS(flted_493_64,
                                                              Anon_18: 
                                                              res::avl<flted_493_64,Anon_18>@M[Orig][LHSCase]@ rem br[{656,655}]&
                                                              (
                                                              ([0<=flted_493_64 & 
                                                                 flted_493_64=s1+
                                                                 s2]
                                                               [0<=Anon_18]))&
                                                              {FLOW,(20,21)=__norm}))
                     
                     })
!!! NEW SPECS: ((None,[]),ECase case {
                   t1=null -> ((None,[]),EBase exists (Expl)(Impl)[s2; 
                                               h2](ex)t2::avl<s2,h2>@M[Orig][LHSCase]@ rem br[{656,655}]&
                                               (([0<=s2][0<=h2]))&
                                               {FLOW,(20,21)=__norm}
                                                 EBase true&(([MayLoop]))&
                                                       {FLOW,(1,23)=__flow}
                                                         EAssume 158::
                                                           EXISTS(h2_4368,
                                                           s3_4369: res::avl<s3_4369,h2_4368>@M[Orig][LHSCase]@ rem br[{656,655}]&
                                                           (
                                                           ([s2=s3_4369 & 
                                                              0<=s2]
                                                            [h2=h2_4368 & 
                                                              0<=h2]
                                                            [null=t1]))&
                                                           {FLOW,(20,21)=__norm}))
                   ;
                   t1!=null -> ((None,[]),EBase exists (Expl)(Impl)[s1; h1; 
                                                s2; 
                                                h2](ex)t1::avl<s1,h1>@M[Orig][LHSCase]@ rem br[{656,655}] * 
                                                t2::avl<s2,h2>@M[Orig][LHSCase]@ rem br[{656,655}]&
                                                (
                                                ([0<=s1][0<=h1][0<=s2][
                                                 0<=h2]))&
                                                {FLOW,(20,21)=__norm}
                                                  EBase true&(([MayLoop]))&
                                                        {FLOW,(1,23)=__flow}
                                                          EAssume 159::
                                                            EXISTS(flted_493_4370,
                                                            Anon_4371: 
                                                            res::avl<flted_493_4370,Anon_4371>@M[Orig][LHSCase]@ rem br[{656,655}]&
                                                            (
                                                            ([0<=flted_493_4370 & 
                                                               0<=s1 & 
                                                               flted_493_4370=s1+
                                                               s2 & 0<=s2]
                                                             [0<=Anon_4371]
                                                             [0<=h2][
                                                             0<=h1][t1!=null]
                                                             ))&
                                                            {FLOW,(20,21)=__norm}))
                   
                   })
!!! NEW RELS:[ (s3=s2 & 0<=s2) --> MRG2(s3,s2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure merge$node~node SUCCESS

Checking procedure rotate_double_left$node~node~node~node~int~int~int... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[am; bm; bn; cm; cn; dm; 
                    an](ex)EXISTS(an_104: a::avl<am,an>@M[Orig][LHSCase]@ rem br[{656,655}] * 
                    b::avl<bm,bn>@M[Orig][LHSCase]@ rem br[{656,655}] * 
                    c::avl<cm,cn>@M[Orig][LHSCase]@ rem br[{656,655}] * 
                    d::avl<dm,an_104>@M[Orig][LHSCase]@ rem br[{656,655}]&(
                    ([an=an_104 & an=max(bn,cn) & 0<=bn & 0<=an & 0<=cn & 
                       (-1+bn)<=cn & (-1+cn)<=bn]
                     [0<=am][0<=bm][0<=cm][0<=dm]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 22::
                                EXISTS(flted_105_103,
                                k: res::avl<k,flted_105_103>@M[Orig][LHSCase]@ rem br[{656,655}]&
                                (
                                ([0<=flted_105_103 & -2+flted_105_103=an]
                                 [0<=k]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[am; bm; bn; cm; cn; dm; 
                  an](ex)a::avl<am,an>@M[Orig][LHSCase]@ rem br[{656,655}] * 
                  b::avl<bm,bn>@M[Orig][LHSCase]@ rem br[{656,655}] * 
                  c::avl<cm,cn>@M[Orig][LHSCase]@ rem br[{656,655}] * 
                  d::avl<dm,an_104>@M[Orig][LHSCase]@ rem br[{656,655}]&(
                  ([0<=am][0<=bm][0<=cm][0<=dm]
                   [an=an_104 & bn<=an & (2*an)<=(1+bn+cn) & cn<=an & 
                     an<=(bn+cn)]
                   ))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 22::
                              EXISTS(k_4537,
                              flted_105_4538: res::avl<k_4537,flted_105_4538>@M[Orig][LHSCase]@ rem br[{656,655}]&
                              (
                              ([(bn=flted_105_4538-2 & cn=flted_105_4538-2 & 
                                 an=flted_105_4538-2 & dm=(((k_4537-cm)-am)-
                                 bm)-3 & 0<=cm & 2<=flted_105_4538 & 
                                 res!=null & 0<=am & 0<=bm & (3+cm+am+
                                 bm)<=k_4537 | bn=flted_105_4538-3 & 
                                 cn=flted_105_4538-2 & an=flted_105_4538-2 & 
                                 dm=(((k_4537-cm)-am)-bm)-3 & 0<=cm & 
                                 res!=null & 3<=flted_105_4538 & 0<=am & 
                                 0<=bm & (3+cm+am+bm)<=k_4537 | 
                                 bn=flted_105_4538-2 & cn=flted_105_4538-3 & 
                                 an=flted_105_4538-2 & dm=(((k_4537-cm)-am)-
                                 bm)-3 & 0<=cm & 3<=flted_105_4538 & 
                                 res!=null & 0<=am & 0<=bm & (3+cm+am+
                                 bm)<=k_4537) & 0<=dm & 0<=an & 0<=cm & 
                                 0<=am & 0<=cn & 0<=bn & 0<=bm]
                               [0<=an_104]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure rotate_double_left$node~node~node~node~int~int~int SUCCESS

Checking procedure rotate_double_right$node~node~node~node~int~int~int... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[am; bm; bn; cm; cn; dm; 
                    an](ex)EXISTS(an_93: a::avl<am,an>@M[Orig][LHSCase]@ rem br[{656,655}] * 
                    b::avl<bm,bn>@M[Orig][LHSCase]@ rem br[{656,655}] * 
                    c::avl<cm,cn>@M[Orig][LHSCase]@ rem br[{656,655}] * 
                    d::avl<dm,an_93>@M[Orig][LHSCase]@ rem br[{656,655}]&(
                    ([an=an_93 & an=max(bn,cn) & 0<=bn & 0<=an & 0<=cn & (-1+
                       cn)<=bn & (-1+bn)<=cn]
                     [0<=am][0<=bm][0<=cm][0<=dm]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 35::
                                EXISTS(flted_136_92,
                                k: res::avl<k,flted_136_92>@M[Orig][LHSCase]@ rem br[{656,655}]&
                                (
                                ([0<=flted_136_92 & -2+flted_136_92=an][
                                 0<=k]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[am; bm; bn; cm; cn; dm; 
                  an](ex)a::avl<am,an>@M[Orig][LHSCase]@ rem br[{656,655}] * 
                  b::avl<bm,bn>@M[Orig][LHSCase]@ rem br[{656,655}] * 
                  c::avl<cm,cn>@M[Orig][LHSCase]@ rem br[{656,655}] * 
                  d::avl<dm,an_93>@M[Orig][LHSCase]@ rem br[{656,655}]&(
                  ([0<=am][0<=bm][0<=cm][0<=dm]
                   [an=an_93 & bn<=an & (2*an)<=(1+bn+cn) & cn<=an & an<=(bn+
                     cn)]
                   ))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 35::
                              EXISTS(k_4704,
                              flted_136_4705: res::avl<k_4704,flted_136_4705>@M[Orig][LHSCase]@ rem br[{656,655}]&
                              (
                              ([(bn=flted_136_4705-2 & cn=flted_136_4705-2 & 
                                 an=flted_136_4705-2 & dm=(((k_4704-cm)-am)-
                                 bm)-3 & 0<=cm & 2<=flted_136_4705 & 
                                 res!=null & 0<=am & 0<=bm & (3+cm+am+
                                 bm)<=k_4704 | bn=flted_136_4705-3 & 
                                 cn=flted_136_4705-2 & an=flted_136_4705-2 & 
                                 dm=(((k_4704-cm)-am)-bm)-3 & 0<=cm & 
                                 res!=null & 3<=flted_136_4705 & 0<=am & 
                                 0<=bm & (3+cm+am+bm)<=k_4704 | 
                                 bn=flted_136_4705-2 & cn=flted_136_4705-3 & 
                                 an=flted_136_4705-2 & dm=(((k_4704-cm)-am)-
                                 bm)-3 & 0<=cm & 3<=flted_136_4705 & 
                                 res!=null & 0<=am & 0<=bm & (3+cm+am+
                                 bm)<=k_4704) & 0<=dm & 0<=an & 0<=cm & 
                                 0<=am & 0<=cn & 0<=bn & 0<=bm]
                               [0<=an_93]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure rotate_double_right$node~node~node~node~int~int~int SUCCESS

Checking procedure rotate_left$node~node~node... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[lm; rlm; ln; rrm](ex)EXISTS(ln_134,
                    flted_42_133: l::avl<lm,ln>@M[Orig][LHSCase]@ rem br[{656,655}] * 
                    rl::avl<rlm,ln_134>@M[Orig][LHSCase]@ rem br[{656,655}] * 
                    rr::avl<rrm,flted_42_133>@M[Orig][LHSCase]@ rem br[{655}]&
                    (
                    ([ln=ln_134 & 0<=ln & -1+flted_42_133=ln][0<=lm][
                     0<=rlm][0<=rrm & 0!=rrm][null!=rr]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 5::
                                EXISTS(flted_43_132,
                                k: res::avl<k,flted_43_132>@M[Orig][LHSCase]@ rem br[{656,655}]&
                                (
                                ([0<=flted_43_132 & -2+flted_43_132=ln][
                                 0<=k]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[lm; rlm; ln; 
                  rrm](ex)l::avl<lm,ln>@M[Orig][LHSCase]@ rem br[{656,655}] * 
                  rl::avl<rlm,ln_134>@M[Orig][LHSCase]@ rem br[{656,655}] * 
                  rr::avl<rrm,flted_42_133>@M[Orig][LHSCase]@ rem br[{655}]&(
                  ([1+ln=flted_42_133 & 1<=flted_42_133 & 1+
                     ln_134=flted_42_133]
                   [0<=lm][0<=rlm][1<=rrm][rr!=null]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 5::
                              EXISTS(k_4775,
                              flted_43_4776: res::avl<k_4775,flted_43_4776>@M[Orig][LHSCase]@ rem br[{656,655}]&
                              (
                              ([k_4775=2+lm+rlm+rrm & 0<=lm & 0<=rlm & 
                                 0<=rrm & 1<=rrm]
                               [rr!=null][-2+flted_43_4776=ln & 0<=ln]
                               [res!=null][0<=flted_42_133][0<=ln_134]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure rotate_left$node~node~node SUCCESS

Checking procedure rotate_right$node~node~node... 
!!! OLD SPECS: ((None,[]),EInfer @post []
              EBase exists (Expl)(Impl)[llm; lln; lrm; 
                    rm](ex)EXISTS(flted_65_117,
                    flted_65_118: ll::avl<llm,lln>@M[Orig][LHSCase]@ rem br[{655}] * 
                    lr::avl<lrm,flted_65_118>@M[Orig][LHSCase]@ rem br[{656,655}] * 
                    r::avl<rm,flted_65_117>@M[Orig][LHSCase]@ rem br[{656,655}]&
                    (
                    ([0<=flted_65_118 & 1+flted_65_117=lln & 1+
                       flted_65_118=lln]
                     [0!=llm & 0<=llm][0<=lrm][0<=rm][null!=ll]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 12::
                                EXISTS(flted_66_116,
                                k: res::avl<k,flted_66_116>@M[Orig][LHSCase]@ rem br[{656,655}]&
                                (
                                ([0<=flted_66_116 & -1+flted_66_116=lln]
                                 [0<=k]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[llm; lln; lrm; 
                  rm](ex)ll::avl<llm,lln>@M[Orig][LHSCase]@ rem br[{655}] * 
                  lr::avl<lrm,flted_65_118>@M[Orig][LHSCase]@ rem br[{656,655}] * 
                  r::avl<rm,flted_65_117>@M[Orig][LHSCase]@ rem br[{656,655}]&
                  (
                  ([flted_65_117=flted_65_118 & -1+lln=flted_65_117 & 
                     0<=flted_65_117]
                   [1<=llm][0<=lrm][0<=rm][ll!=null]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 12::
                              EXISTS(k_4848,
                              flted_66_4849: res::avl<k_4848,flted_66_4849>@M[Orig][LHSCase]@ rem br[{656,655}]&
                              (
                              ([2+llm+lrm+rm=k_4848 & 0<=llm & (3+lrm+
                                 rm)<=k_4848 & 0<=lrm & 0<=rm]
                               [ll!=null]
                               [-1+flted_66_4849=lln & 0<=lln & 1<=lln]
                               [res!=null][0<=flted_65_117][0<=flted_65_118]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure rotate_right$node~node~node SUCCESS

Termination checking result:

Stop Omega... 4536 invocations 
20 false contexts at: ( (501,4)  (501,11)  (506,4)  (506,23)  (506,11)  (505,16)  (505,28)  (505,9)  (504,15)  (504,27)  (504,9)  (504,4)  (384,12)  (380,20)  (324,14)  (320,20)  (253,14)  (249,22)  (232,12)  (228,20) )

Total verification time: 5.18 second(s)
	Time spent in main process: 2.57 second(s)
	Time spent in child processes: 2.61 second(s)
