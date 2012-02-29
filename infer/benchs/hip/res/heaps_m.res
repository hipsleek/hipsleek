
Processing file "heaps_m.ss"
Parsing heaps_m.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure deleteone$int~int~node~node... 
!!! REL :  DELONE(m1,m1',m2,m2')
!!! POST:  (m2'+1)>=m2 & m2>=m2' & m2'+m1'+1=m1+m2
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [DELONE]
              EBase l::pq1@M[Orig][LHSCase]@ rem br[{327,326}] * 
                    r::pq1@M[Orig][LHSCase]@ rem br[{327,326}]&(())&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 36::ref [m1;m2;l;r]
                                l'::pq1@M[Orig][LHSCase]@ rem br[{327,326}] * 
                                r'::pq1@M[Orig][LHSCase]@ rem br[{327,326}]&(
                                ([DELONE(m1,m1',m2,m2')][0<=res]))&
                                {FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase l::pq1@M[Orig][LHSCase]@ rem br[{327,326}] * 
                  r::pq1@M[Orig][LHSCase]@ rem br[{327,326}]&(())&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 36::ref [m1;m2;l;r]
                              l'::pq1@M[Orig][LHSCase]@ rem br[{327,326}] * 
                              r'::pq1@M[Orig][LHSCase]@ rem br[{327,326}]&(
                              ([(-1+m2)<=m2' & m1'+m2'=-1+m1+m2 & m2'<=m2]
                               [0<=res]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (m2'=m2 & -1+m1=m1' & m2<=m1') --> DELONE(m1,m1',m2,m2'),
 (m1'=m1 & -1+m2=m2' & (-1+m1)<=m2') --> DELONE(m1,m1',m2,m2')]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure deleteone$int~int~node~node SUCCESS

Checking procedure deleteoneel$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ t!=null, t!=null, t!=null, t!=null]
!!! OLD SPECS: ((None,[]),EInfer [t,res]
              EBase t::pq1@M[Orig][LHSCase]@ rem br[{327,326}]&(())&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 29::ref [t]
                                t'::pq1@M[Orig][LHSCase]@ rem br[{327,326}]&(
                                ([0<=res]))&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase t::pq1@M[Orig][LHSCase]@ rem br[{327,326}]&(())&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][t!=null]))&{FLOW,(1,23)=__flow}
                            EAssume 29::ref [t]
                              
                              EXISTS(l_1153,
                              r_1154: l_1153::pq1@M[Orig]@ rem br[{327,326}] * 
                              r_1154::pq1@M[Orig]@ rem br[{327,326}]&(
                              ([t!=null][0<=res][null=t']))&
                              {FLOW,(20,21)=__norm})
                              or t'::pq1@M[Orig][LHSCase]@ rem br[{327,326}]&
                                 (([t'=t & t'!=null][0<=res]))&
                                 {FLOW,(20,21)=__norm}
                              )
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure deleteoneel$node SUCCESS

Checking procedure deletemax$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[ inf_left_195_1257::pq1@inf_ann_1375[Orig][LHSCase]@ rem br[{326}], inf_right_195_1258::pq1@inf_ann_1376[Orig][LHSCase]@ rem br[{326}], inf_left_195_1257::pq1@inf_ann_1293[Orig][LHSCase]@ rem br[{327,326}], inf_right_195_1258::pq1@inf_ann_1294[Orig][LHSCase]@ rem br[{327,326}], t::node<inf_val_195_1254,inf_nleft_195_1255,inf_nright_195_1256,inf_left_195_1257,inf_right_195_1258>@inf_ann_1253[Orig][], inf_left_195_1264::pq1@inf_ann_1378[Orig][LHSCase]@ rem br[{326}], inf_right_195_1265::pq1@inf_ann_1379[Orig][LHSCase]@ rem br[{326}], inf_left_195_1264::pq1@inf_ann_1299[Orig][LHSCase]@ rem br[{327,326}], inf_right_195_1265::pq1@inf_ann_1300[Orig][LHSCase]@ rem br[{327,326}], t::node<inf_val_195_1261,inf_nleft_195_1262,inf_nright_195_1263,inf_left_195_1264,inf_right_195_1265>@inf_ann_1260[Orig][], inf_left_195_1271::pq1@inf_ann_1381[Orig][LHSCase]@ rem br[{326}], inf_right_195_1272::pq1@inf_ann_1382[Orig][LHSCase]@ rem br[{326}], inf_left_195_1271::pq1@inf_ann_1305[Orig][LHSCase]@ rem br[{327,326}], inf_right_195_1272::pq1@inf_ann_1306[Orig][LHSCase]@ rem br[{327,326}], t::node<inf_val_195_1268,inf_nleft_195_1269,inf_nright_195_1270,inf_left_195_1271,inf_right_195_1272>@inf_ann_1267[Orig][]]
!!! Inferred Pure :[ t!=null, inf_ann_1375<=0, inf_ann_1376<=0, inf_ann_1293<=0, inf_ann_1294<=0, t!=null, inf_ann_1378<=0, inf_ann_1379<=0, inf_ann_1299<=0, inf_ann_1300<=0, t!=null, inf_ann_1381<=0, inf_ann_1382<=0, inf_ann_1305<=0, inf_ann_1306<=0, t!=null]
!!! OLD SPECS: ((None,[]),EInfer [t]
              EBase t::pq1@M[Orig][LHSCase]@ rem br[{327,326}]&(())&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 59::ref [t]
                                t'::pq1@M[Orig][LHSCase]@ rem br[{327,326}]&(
                                ())&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase t::pq1@M[Orig][LHSCase]@ rem br[{327,326}]&(())&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 59::ref [t]
                              
                              EXISTS(l_1476,
                              r_1477: l_1476::pq1@M[Orig]@ rem br[{327,326}] * 
                              r_1477::pq1@M[Orig]@ rem br[{327,326}]&(
                              ([t!=null][0<=res][null=t']))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(f_1478,tval_1479,tnleft_1480,
                                 tnright_1481,l_1482,
                                 r_1483: t'::node<tval_1479,tnleft_1480,tnright_1481,l_1482,r_1483>@M[Orig][] * 
                                 t'::pq1@M[Orig][LHSCase]@ rem br[{327,326}]&
                                 (
                                 ([t=t' & (0-1)<=tnleft_1480 & (0-
                                    tnright_1481)<=tnleft_1480 & 
                                    tnleft_1480<=0 & 0<=res & t'!=null | 
                                    t=t' & (0-1)<=tnleft_1480 & 
                                    tnleft_1480<=0 & tnleft_1480<=((0-
                                    tnright_1481)-2) & 0<=res & t'!=null]
                                  ))&
                                 {FLOW,(20,21)=__norm})
                              or EXISTS(f_1484,tval_1485,tnleft_1486,
                                 tnright_1487,l_1488,
                                 r_1489: t'::node<tval_1485,tnleft_1486,tnright_1487,l_1488,r_1489>@M[Orig][] * 
                                 t'::pq1@M[Orig][LHSCase]@ rem br[{327,326}]&
                                 (
                                 ([t=t' & (0-tnleft_1486)<=tnright_1487 & (0-
                                    1)<=tnright_1487 & tnright_1487<=0 & 
                                    0<=res & t'!=null | t=t' & (0-
                                    1)<=tnright_1487 & tnright_1487<=((0-
                                    tnleft_1486)-2) & tnright_1487<=0 & 
                                    0<=res & t'!=null]
                                  ))&
                                 {FLOW,(20,21)=__norm})
                              or EXISTS(f_1490,tval_1491,tnleft_1492,
                                 tnright_1493,l_1494,
                                 r_1495: t'::node<tval_1491,tnleft_1492,tnright_1493,l_1494,r_1495>@M[Orig][] * 
                                 t'::pq1@M[Orig][LHSCase]@ rem br[{327,326}]&
                                 (
                                 ([t=t' & 0<=res & 1<=(tnright_1493+
                                    tnleft_1492) & t'!=null & 
                                    0<=tnleft_1492 & 0<=tnright_1493 | 
                                    t=t' & tnright_1493<=(0-1) & 
                                    0<=tnleft_1492 & 0<=res & t'!=null | 
                                    t=t' & tnleft_1492<=(0-1) & t'!=null & 
                                    0<=tnright_1493 & 0<=res | t=t' & 
                                    tnright_1493<=((0-tnleft_1492)-3) & 
                                    tnright_1493<=(0-1) & tnleft_1492<=(0-
                                    1) & t'!=null & 0<=res]
                                  ))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure deletemax$node SUCCESS

Checking procedure insert$node~int... 
!!! OLD SPECS: ((None,[]),EInfer [res,t]
              EBase t::pq1@M[Orig][LHSCase]@ rem br[{327,326}]&(([0<=v]))&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 1::ref [t]
                                res::pq1@M[Orig][LHSCase]@ rem br[{327,326}]&
                                (())&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase t::pq1@M[Orig][LHSCase]@ rem br[{327,326}]&(([0<=v]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 1::ref [t]
                              
                              res::pq1@M[Orig][LHSCase]@ rem br[{327,326}]&(
                              ([0<=v][res!=null][null=t'][null=t]))&
                              {FLOW,(20,21)=__norm}
                              or res::pq1@M[Orig][LHSCase]@ rem br[{327,326}]&
                                 (([0<=v][res=t & res=t' & res!=null]))&
                                 {FLOW,(20,21)=__norm}
                              )
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure insert$node~int SUCCESS

Checking procedure ripple$int~int~int~int~node~node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[]
!!! Inferred Pure :[ l!=null, l!=null, r!=null | l=null, l!=null, r!=null | l=null, l!=null, r!=null | l=null, l!=null, r!=null | l=null, l!=null]
!!! OLD SPECS: ((None,[]),EInfer [l,r]
              EBase l::pq1@M[Orig][LHSCase]@ rem br[{327,326}] * 
                    r::pq1@M[Orig][LHSCase]@ rem br[{327,326}]&(())&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 43::ref [d]
                                l::pq1@M[Orig][LHSCase]@ rem br[{327,326}] * 
                                r::pq1@M[Orig][LHSCase]@ rem br[{327,326}]&(
                                ())&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase l::pq1@M[Orig][LHSCase]@ rem br[{327,326}] * 
                  r::pq1@M[Orig][LHSCase]@ rem br[{327,326}]&(())&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][r!=null][l!=null]))&
                          {FLOW,(1,23)=__flow}
                            EAssume 43::ref [d]
                              
                              l::pq1@M[Orig][LHSCase]@ rem br[{327,326}] * 
                              r::pq1@M[Orig][LHSCase]@ rem br[{327,326}]&(
                              ([v=d'][0=m1][0=m2]))&{FLOW,(20,21)=__norm}
                              or l::pq1@M[Orig][LHSCase]@ rem br[{327,326}] * 
                                 r::pq1@M[Orig][LHSCase]@ rem br[{327,326}]&(
                                 ([m1=0 & d=d' & 1<=m2 | m1=0 & d=d' & 
                                    m2<=(0-1)]
                                  ))&
                                 {FLOW,(20,21)=__norm}
                              or l::pq1@M[Orig][LHSCase]@ rem br[{327,326}] * 
                                 r::pq1@M[Orig][LHSCase]@ rem br[{327,326}]&(
                                 ([m2=0 & v=d' & l!=null & 1<=m1 & 0<=d' | 
                                    m2=0 & v=d' & m1<=(0-1) & l!=null & 0<=d']
                                  ))&
                                 {FLOW,(20,21)=__norm}
                              or l::pq1@M[Orig][LHSCase]@ rem br[{327,326}] * 
                                 r::pq1@M[Orig][LHSCase]@ rem br[{327,326}]&(
                                 ([v=d' & r!=null & 1<=m1 & 1<=m2 & 0<=d' & 
                                    l!=null | v=d' & m2<=(0-1) & r!=null & 
                                    1<=m1 & 0<=d' & l!=null | v=d' & m1<=(0-
                                    1) & r!=null & 1<=m2 & 0<=d' & l!=null | 
                                    v=d' & m2<=(0-1) & m1<=(0-1) & r!=null & 
                                    0<=d' & l!=null]
                                  ))&
                                 {FLOW,(20,21)=__norm}
                              or l::pq1@M[Orig][LHSCase]@ rem br[{327,326}] * 
                                 r::pq1@M[Orig][LHSCase]@ rem br[{327,326}]&(
                                 ([v<d' & r!=null & l!=null & 1<=m1 & 
                                    1<=m2 & 0<=d' | m1<=(0-1) & v<d' & 
                                    r!=null & l!=null & 1<=m2 & 0<=d' | 
                                    m2<=(0-1) & v<d' & r!=null & l!=null & 
                                    1<=m1 & 0<=d' | m1<=(0-1) & m2<=(0-1) & 
                                    v<d' & r!=null & l!=null & 0<=d']
                                  ))&
                                 {FLOW,(20,21)=__norm}
                              )
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure ripple$int~int~int~int~node~node SUCCESS

Termination checking result:

Stop Omega... 1258 invocations 
0 false contexts at: ()

Total verification time: 1.49 second(s)
	Time spent in main process: 0.38 second(s)
	Time spent in child processes: 1.11 second(s)
