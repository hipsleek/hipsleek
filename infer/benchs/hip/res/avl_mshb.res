
Processing file "avl_mshb.ss"
Parsing avl_mshb.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure build_avl1$node~node... 
Procedure build_avl1$node~node SUCCESS

Checking procedure build_avl2$node~node~node... 
Procedure build_avl2$node~node~node SUCCESS

Checking procedure get_max$int~int... 
Procedure get_max$int~int SUCCESS

Checking procedure height$node... 
!!! REL :  H(b,b2)
!!! POST:  b2>=0 & 2>=b2 & b2=b
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [H]
              EBase exists (Expl)(Impl)[m; n; 
                    b](ex)x::avl2<m,n,b>@M[Orig][LHSCase]@ rem br[{656,655}]&
                    (([0<=m][0<=n][b<=2 & 0<=b]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 2::
                                EXISTS(m_178,n_179,
                                b2: x::avl2<m_178,n_179,b2>@M[Orig][LHSCase]@ rem br[{656,655}]&
                                (
                                ([0<=b2 & b2<=2 & H(b,b2)]
                                 [m=m_178 & 0<=m_178]
                                 [n=n_179 & n=res & 0<=n_179]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[m; n; 
                  b](ex)x::avl2<m,n,b>@M[Orig][LHSCase]@ rem br[{656,655}]&(
                  ([0<=m][0<=n][0<=b & b<=2]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 2::
                              EXISTS(m_2166,n_2167,
                              b2_2168: x::avl2<m_2166,n_2167,b2_2168>@M[Orig][LHSCase]@ rem br[{656,655}]&
                              (
                              ([b=b2_2168 & b<=2 & 0<=b]
                               [res=n & res=n_2167 & 0<=n][m=m_2166 & 0<=m]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (b=1 & b2=1) --> H(b,b2),
 (b2=b & 0<=b & b<=2) --> H(b,b2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure height$node SUCCESS

Checking procedure rotate_double_left$node~node~node~node~int~int~int... 
Procedure rotate_double_left$node~node~node~node~int~int~int SUCCESS

Checking procedure rotate_double_right$node~node~node~node~int~int~int... 
Procedure rotate_double_right$node~node~node~node~int~int~int SUCCESS

Checking procedure rotate_left$node~node~node... 
Procedure rotate_left$node~node~node SUCCESS

Checking procedure rotate_right$node~node~node... 
Procedure rotate_right$node~node~node SUCCESS

Checking procedure insert$node~int... 
!!! REL :  INS1(b)
!!! POST:  1=b
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [INS,INS1]
              ECase case {
                     x=null -> ((None,[]),EBase true&MayLoop&
                                                {FLOW,(1,23)=__flow}
                                                  EAssume 54::
                                                    EXISTS(flted_177_116,
                                                    flted_177_117,
                                                    b: res::avl2<flted_177_117,flted_177_116,b>@M[Orig][LHSCase]@ rem br[{655}]&
                                                    (
                                                    ([1=flted_177_117]
                                                     [1=flted_177_116]
                                                     [0<=b & b<=2 & INS1(b)]
                                                     [null!=res]))&
                                                    {FLOW,(20,21)=__norm}))
                     ;
                     x!=null -> ((None,[]),EBase exists (Expl)(Impl)[tm; tn; 
                                                 b](ex)x::avl2<tm,tn,b>@M[Orig][LHSCase]@ rem br[{656,655}]&
                                                 (
                                                 ([0<=tm][0<=tn][b<=2 & 0<=b]
                                                  ))&
                                                 {FLOW,(20,21)=__norm}
                                                   EBase true&MayLoop&
                                                         {FLOW,(1,23)=__flow}
                                                           EAssume 55::
                                                             EXISTS(flted_180_115,
                                                             resn,
                                                             resb: res::avl2<flted_180_115,resn,resb>@M[Orig][LHSCase]@ rem br[{655}]&
                                                             (
                                                             ([1<=tm & -1+
                                                                flted_180_115=tm]
                                                              [(tn=resn | 
                                                                resn=1+tn & 
                                                                INS(resb)) & 
                                                                0<=resn & 
                                                                0<=resb & 
                                                                0!=resn & 
                                                                resb<=2 & 
                                                                1<=tn]
                                                              [null!=res]))&
                                                             {FLOW,(20,21)=__norm}))
                     
                     })
!!! NEW SPECS: ((None,[]),ECase case {
                   x=null -> ((None,[]),EBase true&(([MayLoop]))&
                                              {FLOW,(1,23)=__flow}
                                                EAssume 54::
                                                  EXISTS(flted_177_4200,
                                                  flted_177_4201,
                                                  b_4202: res::avl2<flted_177_4201,flted_177_4200,b_4202>@M[Orig][LHSCase]@ rem br[{655}]&
                                                  (
                                                  ([1=b_4202 & 0<=b_4202 & 
                                                     b_4202<=2]
                                                   [null!=res]
                                                   [1=flted_177_4200]
                                                   [1=flted_177_4201][
                                                   null=x]))&
                                                  {FLOW,(20,21)=__norm}))
                   ;
                   x!=null -> ((None,[]),EBase exists (Expl)(Impl)[tm; tn; 
                                               b](ex)x::avl2<tm,tn,b>@M[Orig][LHSCase]@ rem br[{656,655}]&
                                               (
                                               ([0<=tm][0<=tn][0<=b & b<=2]))&
                                               {FLOW,(20,21)=__norm}
                                                 EBase true&(([MayLoop]))&
                                                       {FLOW,(1,23)=__flow}
                                                         EAssume 55::
                                                           EXISTS(flted_180_4203,
                                                           resn_4204,
                                                           resb_4205: 
                                                           res::avl2<flted_180_4203,resn_4204,resb_4205>@M[Orig][LHSCase]@ rem br[{655}]&
                                                           (
                                                           ([null!=res]
                                                            [(tn=resn_4204 | 
                                                              resn_4204=1+
                                                              tn & true) & 
                                                              0<=resn_4204 & 
                                                              0<=tn & 
                                                              1<=tn & 
                                                              0!=resn_4204]
                                                            [0<=resb_4205 & 
                                                              resb_4205<=2]
                                                            [1<=tm & 0<=tm & 
                                                              -1+
                                                              flted_180_4203=tm]
                                                            [0<=b & b<=2]
                                                            [x!=null]))&
                                                           {FLOW,(20,21)=__norm}))
                   
                   })
!!! NEW RELS:[ (b=1) --> INS1(b)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure insert$node~int SUCCESS

Checking procedure insert_inline$node~int... 
!!! REL :  INSI(b)
!!! POST:  1=b
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [INSI]
              ECase case {
                     x=null -> ((None,[]),EBase true&MayLoop&
                                                {FLOW,(1,23)=__flow}
                                                  EAssume 72::
                                                    EXISTS(flted_246_102,
                                                    flted_246_103,
                                                    b: res::avl2<flted_246_103,flted_246_102,b>@M[Orig][LHSCase]@ rem br[{655}]&
                                                    (
                                                    ([1=flted_246_103]
                                                     [1=flted_246_102]
                                                     [0<=b & b<=2 & INSI(b)]
                                                     [null!=res]))&
                                                    {FLOW,(20,21)=__norm}))
                     ;
                     x!=null -> ((None,[]),EBase exists (Expl)(Impl)[tm; tn; 
                                                 b](ex)x::avl2<tm,tn,b>@M[Orig][LHSCase]@ rem br[{656,655}]&
                                                 (
                                                 ([0<=tm][0<=tn][b<=2 & 0<=b]
                                                  ))&
                                                 {FLOW,(20,21)=__norm}
                                                   EBase true&MayLoop&
                                                         {FLOW,(1,23)=__flow}
                                                           EAssume 73::
                                                             EXISTS(flted_249_101,
                                                             resn,
                                                             resb: res::avl2<flted_249_101,resn,resb>@M[Orig][LHSCase]@ rem br[{655}]&
                                                             (
                                                             ([1<=tm & -1+
                                                                flted_249_101=tm]
                                                              [(tn=resn | 
                                                                resn=1+tn & 
                                                                resb!=1) & 
                                                                0<=resn & 
                                                                0<=resb & 
                                                                0!=resn & 
                                                                resb<=2 & 
                                                                1<=tn]
                                                              [null!=res]))&
                                                             {FLOW,(20,21)=__norm}))
                     
                     })
!!! NEW SPECS: ((None,[]),ECase case {
                   x=null -> ((None,[]),EBase true&(([MayLoop]))&
                                              {FLOW,(1,23)=__flow}
                                                EAssume 72::
                                                  EXISTS(flted_246_6263,
                                                  flted_246_6264,
                                                  b_6265: res::avl2<flted_246_6264,flted_246_6263,b_6265>@M[Orig][LHSCase]@ rem br[{655}]&
                                                  (
                                                  ([1=b_6265 & 0<=b_6265 & 
                                                     b_6265<=2]
                                                   [null!=res]
                                                   [1=flted_246_6263]
                                                   [1=flted_246_6264][
                                                   null=x]))&
                                                  {FLOW,(20,21)=__norm}))
                   ;
                   x!=null -> ((None,[]),EBase exists (Expl)(Impl)[tm; tn; 
                                               b](ex)x::avl2<tm,tn,b>@M[Orig][LHSCase]@ rem br[{656,655}]&
                                               (
                                               ([0<=tm][0<=tn][0<=b & b<=2]))&
                                               {FLOW,(20,21)=__norm}
                                                 EBase true&(([MayLoop]))&
                                                       {FLOW,(1,23)=__flow}
                                                         EAssume 73::
                                                           EXISTS(flted_249_6266,
                                                           resn_6267,
                                                           resb_6268: 
                                                           res::avl2<flted_249_6266,resn_6267,resb_6268>@M[Orig][LHSCase]@ rem br[{655}]&
                                                           (
                                                           ([null!=res]
                                                            [(tn=resn_6267 | 
                                                              resn_6267=1+
                                                              tn & 
                                                              resb_6268!=1) & 
                                                              0<=resn_6267 & 
                                                              0<=tn & 
                                                              1<=tn & 
                                                              0!=resn_6267 & 
                                                              0<=resb_6268 & 
                                                              resb_6268<=2]
                                                            [1<=tm & 0<=tm & 
                                                              -1+
                                                              flted_249_6266=tm]
                                                            [0<=b & b<=2]
                                                            [x!=null]))&
                                                           {FLOW,(20,21)=__norm}))
                   
                   })
!!! NEW RELS:[ (b=1) --> INSI(b)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure insert_inline$node~int SUCCESS

Checking procedure merge$node~node... 
!!! REL :  MRG1(b2,b3)
!!! POST:  b2>=0 & 2>=b2 & b2=b3
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [MRG1]
              EBase exists (Expl)(Impl)[s2; h2; 
                    b2](ex)t2::avl2<s2,h2,b2>@M[Orig][LHSCase]@ rem br[{656,655}]&
                    (([0<=s2][0<=h2][b2<=2 & 0<=b2]))&{FLOW,(20,21)=__norm}
                      ECase case {
                             t1=null -> ((None,[]),EBase true&MayLoop&
                                                         {FLOW,(1,23)=__flow}
                                                           EAssume 156::
                                                             EXISTS(s2_94,
                                                             h2_95,
                                                             b3: res::avl2<s2_94,h2_95,b3>@M[Orig][LHSCase]@ rem br[{656,655}]&
                                                             (
                                                             ([0<=b3 & 
                                                                b3<=2 & 
                                                                MRG1(b2,b3)]
                                                              [s2=s2_94 & 
                                                                0<=s2_94]
                                                              [h2=h2_95 & 
                                                                0<=h2_95]
                                                              ))&
                                                             {FLOW,(20,21)=__norm}))
                             ;
                             t1!=null -> ((None,[]),EBase exists (Expl)(Impl)[s1; 
                                                          h1; 
                                                          Anon_43](ex)
                                                          t1::avl2<s1,h1,Anon_43>@M[Orig][LHSCase]@ rem br[{656,655}]&
                                                          (
                                                          ([0<=s1][0<=h1]
                                                           [Anon_43<=2 & 
                                                             0<=Anon_43]
                                                           ))&
                                                          {FLOW,(20,21)=__norm}
                                                            EBase true&
                                                                  MayLoop&
                                                                  {FLOW,(1,23)=__flow}
                                                                    EAssume 157::
                                                                    EXISTS(flted_481_93,
                                                                    Anon_44,
                                                                    Anon_45: 
                                                                    res::avl2<flted_481_93,Anon_44,Anon_45>@M[Orig][LHSCase]@ rem br[{656,655}]&
                                                                    (
                                                                    ([
                                                                    0<=flted_481_93 & 
                                                                    flted_481_93=s1+
                                                                    s2]
                                                                    [Anon_45<=2 & 
                                                                    0<=Anon_45]
                                                                    [0<=Anon_44]
                                                                    ))&
                                                                    {FLOW,(20,21)=__norm}))
                             
                             })
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[s2; h2; 
                  b2](ex)t2::avl2<s2,h2,b2>@M[Orig][LHSCase]@ rem br[{656,655}]&
                  (([0<=s2][0<=h2][0<=b2 & b2<=2]))&{FLOW,(20,21)=__norm}
                    ECase case {
                           t1=null -> ((None,[]),EBase true&(([MayLoop]))&
                                                       {FLOW,(1,23)=__flow}
                                                         EAssume 156::
                                                           EXISTS(s2_6533,
                                                           h2_6534,
                                                           b3_6535: res::avl2<s2_6533,h2_6534,b3_6535>@M[Orig][LHSCase]@ rem br[{656,655}]&
                                                           (
                                                           ([b2=b3_6535 & 
                                                              b2<=2 & 0<=b2]
                                                            [h2=h2_6534 & 
                                                              0<=h2]
                                                            [s2=s2_6533 & 
                                                              0<=s2]
                                                            [null=t1]))&
                                                           {FLOW,(20,21)=__norm}))
                           ;
                           t1!=null -> ((None,[]),EBase exists (Expl)(Impl)[s1; 
                                                        h1; 
                                                        Anon_43](ex)t1::avl2<s1,h1,Anon_43>@M[Orig][LHSCase]@ rem br[{656,655}]&
                                                        (
                                                        ([0<=s1][0<=h1]
                                                         [Anon_43<=2 & 
                                                           0<=Anon_43]
                                                         ))&
                                                        {FLOW,(20,21)=__norm}
                                                          EBase true&(
                                                                ([MayLoop]))&
                                                                {FLOW,(1,23)=__flow}
                                                                  EAssume 157::
                                                                    EXISTS(flted_481_6536,
                                                                    Anon_6537,
                                                                    Anon_6538: 
                                                                    res::avl2<flted_481_6536,Anon_6537,Anon_6538>@M[Orig][LHSCase]@ rem br[{656,655}]&
                                                                    (
                                                                    ([
                                                                    0<=flted_481_6536 & 
                                                                    0<=s2 & 
                                                                    flted_481_6536=s1+
                                                                    s2 & 
                                                                    0<=s1]
                                                                    [0<=Anon_6538 & 
                                                                    Anon_6538<=2]
                                                                    [0<=Anon_6537]
                                                                    [0<=h1]
                                                                    [0<=h2]
                                                                    [0<=b2 & 
                                                                    b2<=2]
                                                                    [t1!=null]
                                                                    [Anon_43<=2 & 
                                                                    0<=Anon_43]
                                                                    ))&
                                                                    {FLOW,(20,21)=__norm}))
                           
                           })
!!! NEW RELS:[ (b3=b2 & 0<=b2 & b2<=2) --> MRG1(b2,b3)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure merge$node~node SUCCESS

Termination checking result:

Stop Omega... 5538 invocations 
313 false contexts at: ( (485,17)  (485,24)  (489,3)  (489,22)  (489,10)  (488,15)  (488,27)  (488,8)  (487,14)  (487,26)  (487,8)  (487,3)  (262,2)  (262,21)  (262,9)  (377,12)  (377,19)  (373,20)  (373,27)  (370,22)  (370,29)  (368,34)  (368,36)  (368,22)  (367,26)  (367,46)  (367,34)  (367,22)  (365,22)  (364,26)  (364,30)  (364,22)  (363,26)  (363,22)  (362,27)  (362,35)  (362,22)  (360,22)  (359,26)  (359,30)  (359,22)  (358,26)  (358,22)  (357,27)  (357,35)  (357,22)  (355,22)  (354,28)  (354,36)  (354,22)  (353,22)  (352,27)  (352,35)  (352,22)  (351,32)  (351,22)  (350,32)  (350,22)  (348,27)  (348,22)  (348,22)  (346,56)  (346,48)  (346,42)  (346,31)  (346,23)  (346,23)  (346,22)  (346,18)  (342,18)  (342,25)  (340,18)  (339,22)  (339,26)  (339,18)  (338,22)  (338,30)  (338,18)  (337,23)  (337,31)  (337,18)  (335,18)  (334,22)  (334,26)  (334,18)  (333,22)  (333,18)  (332,23)  (332,31)  (332,18)  (330,18)  (329,23)  (329,31)  (329,18)  (328,28)  (328,18)  (328,18)  (326,46)  (326,38)  (326,26)  (326,18)  (326,18)  (325,19)  (325,14)  (325,14)  (323,54)  (323,42)  (323,34)  (323,23)  (323,15)  (323,15)  (323,14)  (322,20)  (322,10)  (321,16)  (321,10)  (321,10)  (317,14)  (317,21)  (313,20)  (313,27)  (310,22)  (310,29)  (308,22)  (307,26)  (307,30)  (307,22)  (306,26)  (306,47)  (306,34)  (306,22)  (304,22)  (303,26)  (303,30)  (303,22)  (302,26)  (302,22)  (301,27)  (301,35)  (301,22)  (299,22)  (298,26)  (298,30)  (298,22)  (297,26)  (297,22)  (296,27)  (296,35)  (296,22)  (294,22)  (293,28)  (293,36)  (293,22)  (292,22)  (291,27)  (291,35)  (291,22)  (290,33)  (290,22)  (289,31)  (289,22)  (288,27)  (288,22)  (288,22)  (286,63)  (286,51)  (286,43)  (286,43)  (286,30)  (286,22)  (286,22)  (286,18)  (282,18)  (282,25)  (281,18)  (280,22)  (280,26)  (280,18)  (279,22)  (279,38)  (279,30)  (279,18)  (278,18)  (277,22)  (277,26)  (277,18)  (276,18)  (275,22)  (275,56)  (275,49)  (275,38)  (275,30)  (275,18)  (274,27)  (274,18)  (274,18)  (272,45)  (272,37)  (272,26)  (272,18)  (272,18)  (271,19)  (271,14)  (271,14)  (269,54)  (269,41)  (269,33)  (269,23)  (269,15)  (269,15)  (269,14)  (268,19)  (268,10)  (267,16)  (267,10)  (267,10)  (265,11)  (265,6)  (265,2)  (190,2)  (190,22)  (190,9)  (234,14)  (234,21)  (230,22)  (230,29)  (228,22)  (228,117)  (228,114)  (228,111)  (228,96)  (228,76)  (228,57)  (228,49)  (228,29)  (227,48)  (227,40)  (227,34)  (227,18)  (227,10)  (227,10)  (227,9)  (227,5)  (223,5)  (223,46)  (223,32)  (223,24)  (223,12)  (221,41)  (221,33)  (221,16)  (221,8)  (221,8)  (221,4)  (219,47)  (219,35)  (219,27)  (219,16)  (219,8)  (219,8)  (219,7)  (218,13)  (218,3)  (217,9)  (217,3)  (217,3)  (213,12)  (213,19)  (209,20)  (209,27)  (207,20)  (207,113)  (207,110)  (207,107)  (207,98)  (207,78)  (207,59)  (207,46)  (207,27)  (206,71)  (206,55)  (206,47)  (206,47)  (206,30)  (206,22)  (206,22)  (206,18)  (202,18)  (202,65)  (202,51)  (202,38)  (202,25)  (200,49)  (200,41)  (200,26)  (200,18)  (200,18)  (200,14)  (198,54)  (198,41)  (198,33)  (198,23)  (198,15)  (198,15)  (198,14)  (196,19)  (196,10)  (195,16)  (195,10)  (195,10)  (193,11)  (193,6)  (193,2) )

Total verification time: 11.05 second(s)
	Time spent in main process: 5.38 second(s)
	Time spent in child processes: 5.67 second(s)
