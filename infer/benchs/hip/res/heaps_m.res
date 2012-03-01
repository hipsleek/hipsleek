
Processing file "heaps_m.ss"
Parsing heaps_m.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure deletemax$node... 
!!! >>>>>> HIP gather infer pre <<<<<<
!!! Inferred Heap :[ inf_left_204_1059::pq1@inf_ann_1177[Orig][LHSCase]@ rem br[{328}], inf_right_204_1060::pq1@inf_ann_1178[Orig][LHSCase]@ rem br[{328}], inf_left_204_1059::pq1@inf_ann_1095[Orig][LHSCase]@ rem br[{328}], inf_right_204_1060::pq1@inf_ann_1096[Orig][LHSCase]@ rem br[{328}], t::node<inf_val_204_1056,inf_nleft_204_1057,inf_nright_204_1058,inf_left_204_1059,inf_right_204_1060>@inf_ann_1055[Orig][], inf_left_204_1066::pq1@inf_ann_1180[Orig][LHSCase]@ rem br[{328}], inf_right_204_1067::pq1@inf_ann_1181[Orig][LHSCase]@ rem br[{328}], inf_left_204_1066::pq1@inf_ann_1101[Orig][LHSCase]@ rem br[{328}], inf_right_204_1067::pq1@inf_ann_1102[Orig][LHSCase]@ rem br[{328}], t::node<inf_val_204_1063,inf_nleft_204_1064,inf_nright_204_1065,inf_left_204_1066,inf_right_204_1067>@inf_ann_1062[Orig][], inf_left_204_1073::pq1@inf_ann_1183[Orig][LHSCase]@ rem br[{328}], inf_right_204_1074::pq1@inf_ann_1184[Orig][LHSCase]@ rem br[{328}], inf_left_204_1073::pq1@inf_ann_1107[Orig][LHSCase]@ rem br[{328}], inf_right_204_1074::pq1@inf_ann_1108[Orig][LHSCase]@ rem br[{328}], t::node<inf_val_204_1070,inf_nleft_204_1071,inf_nright_204_1072,inf_left_204_1073,inf_right_204_1074>@inf_ann_1069[Orig][]]
!!! Inferred Pure :[ t!=null, inf_ann_1177<=0, inf_ann_1178<=0, inf_ann_1095<=0, inf_ann_1096<=0, t!=null, inf_ann_1180<=0, inf_ann_1181<=0, inf_ann_1101<=0, inf_ann_1102<=0, t!=null, inf_ann_1183<=0, inf_ann_1184<=0, inf_ann_1107<=0, inf_ann_1108<=0, t!=null]
!!! OLD SPECS: ((None,[]),EInfer [t]
              EBase t::pq1@M[Orig][LHSCase]@ rem br[{329,328}]&(())&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 61::ref [t]
                                t'::pq1@M[Orig][LHSCase]@ rem br[{329,328}]&(
                                ())&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase t::pq1@M[Orig][LHSCase]@ rem br[{329,328}]&(())&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 61::ref [t]
                              
                              EXISTS(l_1278,
                              r_1279: l_1278::pq1@M[Orig]@ rem br[{329,328}] * 
                              r_1279::pq1@M[Orig]@ rem br[{329,328}]&(
                              ([t!=null][0<=res][null=t']))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(f_1280,tval_1281,tnleft_1282,
                                 tnright_1283,l_1284,
                                 r_1285: t'::node<tval_1281,tnleft_1282,tnright_1283,l_1284,r_1285>@M[Orig][] * 
                                 t'::pq1@M[Orig][LHSCase]@ rem br[{329,328}]&
                                 (
                                 ([t=t' & (0-1)<=tnleft_1282 & (0-
                                    tnright_1283)<=tnleft_1282 & 
                                    tnleft_1282<=0 & 0<=res & t'!=null | 
                                    t=t' & (0-1)<=tnleft_1282 & 
                                    tnleft_1282<=0 & tnleft_1282<=((0-
                                    tnright_1283)-2) & 0<=res & t'!=null]
                                  ))&
                                 {FLOW,(20,21)=__norm})
                              or EXISTS(f_1286,tval_1287,tnleft_1288,
                                 tnright_1289,l_1290,
                                 r_1291: t'::node<tval_1287,tnleft_1288,tnright_1289,l_1290,r_1291>@M[Orig][] * 
                                 t'::pq1@M[Orig][LHSCase]@ rem br[{329,328}]&
                                 (
                                 ([t=t' & (0-tnleft_1288)<=tnright_1289 & (0-
                                    1)<=tnright_1289 & tnright_1289<=0 & 
                                    0<=res & t'!=null | t=t' & (0-
                                    1)<=tnright_1289 & tnright_1289<=((0-
                                    tnleft_1288)-2) & tnright_1289<=0 & 
                                    0<=res & t'!=null]
                                  ))&
                                 {FLOW,(20,21)=__norm})
                              or EXISTS(f_1292,tval_1293,tnleft_1294,
                                 tnright_1295,l_1296,
                                 r_1297: t'::node<tval_1293,tnleft_1294,tnright_1295,l_1296,r_1297>@M[Orig][] * 
                                 t'::pq1@M[Orig][LHSCase]@ rem br[{329,328}]&
                                 (
                                 ([t=t' & 0<=res & 1<=(tnright_1295+
                                    tnleft_1294) & t'!=null & 
                                    0<=tnleft_1294 & 0<=tnright_1295 | 
                                    t=t' & tnright_1295<=(0-1) & 0<=res & 
                                    t'!=null & 0<=tnleft_1294 | t=t' & 
                                    tnleft_1294<=(0-1) & t'!=null & 
                                    0<=tnright_1295 & 0<=res | t=t' & 
                                    tnright_1295<=((0-tnleft_1294)-3) & 
                                    tnright_1295<=(0-1) & tnleft_1294<=(0-
                                    1) & 0<=res & t'!=null]
                                  ))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure deletemax$node SUCCESS

Checking procedure deleteone$int~int~node~node... 
!!! REL :  DELONE(m1,m1',m2,m2')
!!! POST:  (m2'+1)>=m2 & m2>=m2' & m2'+m1'+1=m1+m2
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [DELONE]
              EBase l::pq1@M[Orig][LHSCase]@ rem br[{328}] * 
                    r::pq1@M[Orig][LHSCase]@ rem br[{328}]&(
                    ([null!=l][null!=r]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 38::ref [m1;m2;l;r]
                                l'::pq1@M[Orig][LHSCase]@ rem br[{329,328}] * 
                                r'::pq1@M[Orig][LHSCase]@ rem br[{329,328}]&(
                                ([DELONE(m1,m1',m2,m2')][0<=res]))&
                                {FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase l::pq1@M[Orig][LHSCase]@ rem br[{328}] * 
                  r::pq1@M[Orig][LHSCase]@ rem br[{328}]&(
                  ([l!=null][r!=null]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 38::ref [m1;m2;l;r]
                              l'::pq1@M[Orig][LHSCase]@ rem br[{329,328}] * 
                              r'::pq1@M[Orig][LHSCase]@ rem br[{329,328}]&(
                              ([(-1+m2)<=m2' & m1'+m2'=-1+m1+m2 & m2'<=m2]
                               [0<=res]))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (m2=m2' & m1'=m1-1 & m2'<m1) --> DELONE(m1,m1',m2,m2'),
 (m1=m1' & m2'=m2-1 & m1'<=m2) --> DELONE(m1,m1',m2,m2')]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure deleteone$int~int~node~node SUCCESS

Checking procedure deleteoneel$node... 
Procedure Call:heaps_m.ss:97: 9: 
Verification Context:(Line:80,Col:9)
Proving precondition in method deleteone1$int~int~node~node for spec:
 ((None,[]),EBase tleft_65'::pq1@M[Orig][LHSCase]@ rem br[{328}] * 
                  tright_66'::pq1@M[Orig][LHSCase]@ rem br[{328}]&(
                  ([null!=tleft_65'][null!=tright_66']))&
                  {FLOW,(20,21)=__norm}
                    EBase true&MayLoop&{FLOW,(1,23)=__flow}
                            EAssume 37::ref [tnleft_63;tnright_64;tleft_65;tright_66]
                              tleft_65'::pq1@M[Orig][LHSCase]@ rem br[{329,328}] * 
                              tright_66'::pq1@M[Orig][LHSCase]@ rem br[{329,328}]&
                              (
                              ([0<=res]
                               [tnright_64'<=tnright_64 & tnleft_63'+
                                 tnright_64'=-1+tnleft_63+tnright_64 & (-1+
                                 tnright_64)<=tnright_64']
                               ))&
                              {FLOW,(20,21)=__norm})
Current States: [ or[l_1351::pq1@M[Orig]@ rem br[{329,328}] * r_1352::pq1@M[Orig]@ rem br[{329,328}]&(([
                                                                    !(v_bool_86_792')]
                                                                    [635::!(v_boolean_86_1417)]
                                                                    [m2_1350=tnright_64' & 
                                                                    m2_1350!=0]
                                                                    [d_1348=tval_62' & 
                                                                    0<=d_1348]
                                                                    [t'=t & 
                                                                    t'!=null]
                                                                    [m1_1349=tnleft_63' & 
                                                                    m1_1349=0]
                                                                    [v_boolean_86_1416]
                                                                    [r_1352=tright_66']
                                                                    [l_1351=tleft_65']
                                                                    ))&{FLOW,(20,21)=__norm}
    es_infer_vars/rel: [t; res]
    es_infer_pure: [t!=null]
    es_var_measures: MayLoop; 
l_1351::pq1@M[Orig]@ rem br[{329,328}] * r_1352::pq1@M[Orig]@ rem br[{329,328}]&(([
                                                                    !(v_bool_86_792')]
                                                                    [v_boolean_86_1421]
                                                                    [m2_1350=tnright_64' & 
                                                                    m2_1350=0]
                                                                    [d_1348=tval_62' & 
                                                                    0<=d_1348]
                                                                    [t=t' & 
                                                                    t'!=null]
                                                                    [m1_1349=tnleft_63' & 
                                                                    m1_1349!=0]
                                                                    [640::!(v_boolean_86_1420)]
                                                                    [r_1352=tright_66']
                                                                    [l_1351=tleft_65']
                                                                    ))&{FLOW,(20,21)=__norm}
es_infer_vars/rel: [t; res]
es_infer_pure: [t!=null]
es_var_measures: MayLoop; 
l_1351::pq1@M[Orig]@ rem br[{329,328}] * r_1352::pq1@M[Orig]@ rem br[{329,328}]&(([
                                                                    !(v_bool_86_792')]
                                                                    [617::!(v_boolean_86_1425)]
                                                                    [m2_1350=tnright_64' & 
                                                                    m2_1350!=0]
                                                                    [d_1348=tval_62' & 
                                                                    0<=d_1348]
                                                                    [t'=t & 
                                                                    t'!=null]
                                                                    [m1_1349=tnleft_63' & 
                                                                    m1_1349!=0]
                                                                    [640::!(v_boolean_86_1424)]
                                                                    [r_1352=tright_66']
                                                                    [l_1351=tleft_65']
                                                                    ))&{FLOW,(20,21)=__norm}
es_infer_vars/rel: [t; res]
es_infer_pure: [t!=null]
es_var_measures: MayLoop]] has failed 


!!! OLD SPECS: ((None,[]),EInfer [t,res]
              EBase t::pq1@M[Orig][LHSCase]@ rem br[{329,328}]&(())&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 30::ref [t]
                                t'::pq1@M[Orig][LHSCase]@ rem br[{329,328}]&(
                                ())&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase t::pq1@M[Orig][LHSCase]@ rem br[{329,328}]&(())&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 30::ref [t]
                              t'::pq1@M[Orig][LHSCase]@ rem br[{329,328}]&(
                              ())&{FLOW,(20,21)=__norm})
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure deleteoneel$node result FAIL-1

Checking procedure insert$node~int... 
!!! OLD SPECS: ((None,[]),EInfer [res,t]
              EBase t::pq1@M[Orig][LHSCase]@ rem br[{329,328}]&(([0<=v]))&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 1::ref [t]
                                res::pq1@M[Orig][LHSCase]@ rem br[{329,328}]&
                                (())&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase t::pq1@M[Orig][LHSCase]@ rem br[{329,328}]&(([0<=v]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 1::ref [t]
                              
                              res::pq1@M[Orig][LHSCase]@ rem br[{329,328}]&(
                              ([0<=v][res!=null][null=t'][null=t]))&
                              {FLOW,(20,21)=__norm}
                              or res::pq1@M[Orig][LHSCase]@ rem br[{329,328}]&
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
!!! REL :  RP(d,v,m1,m2)
!!! POST:  m2>=1 | 0>=(1+m2) | 0=m2 & 0=m1 | v>=0 & 0=m2
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [l,r,RP]
              EBase l::pq1@M[Orig][LHSCase]@ rem br[{329,328}] * 
                    r::pq1@M[Orig][LHSCase]@ rem br[{329,328}]&(())&
                    {FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 45::ref [d]
                                l::pq1@M[Orig][LHSCase]@ rem br[{329,328}] * 
                                r::pq1@M[Orig][LHSCase]@ rem br[{329,328}]&(
                                ([RP(d,v,m1,m2)]))&{FLOW,(20,21)=__norm})
!!! NEW SPECS: ((None,[]),EBase l::pq1@M[Orig][LHSCase]@ rem br[{329,328}] * 
                  r::pq1@M[Orig][LHSCase]@ rem br[{329,328}]&(())&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][r!=null][l!=null]))&
                          {FLOW,(1,23)=__flow}
                            EAssume 45::ref [d]
                              l::pq1@M[Orig][LHSCase]@ rem br[{329,328}] * 
                              r::pq1@M[Orig][LHSCase]@ rem br[{329,328}]&(
                              ([m2>=1 | 0>=(1+m2) | 0=m2 & 0=m1 | v>=0 & 0=m2]
                               ))&
                              {FLOW,(20,21)=__norm})
!!! NEW RELS:[ (m2=0 & m1=0) --> RP(d,v,m1,m2),
 (m1=0 & 1<=m2 | m1=0 & m2<=(0-1)) --> RP(d,v,m1,m2),
 (m2=0 & 1<=m1 & 0<=v | m2=0 & m1<=(0-1) & 0<=v) --> RP(d,v,m1,m2),
 (1<=m2 & 1<=m1 & 0<=v | m2<=(0-1) & m1<=(0-1) & 0<=v | m1<=(0-1) & 1<=m2 & 
  0<=v | m2<=(0-1) & 1<=m1 & 0<=v) --> RP(d,v,m1,m2),
 ((v<d' & 1<=m2 & 0<=d' & 1<=m1 | m1<=(0-1) & v<d' & m2<=(0-1) & 0<=d' | 
  v<d' & m2<=(0-1) & 0<=d' & 1<=m1 | m1<=(0-1) & v<d' & 0<=d' & 1<=m2) & 
  RP(d',v,m1_1793,m2_1794)) --> RP(d,v,m1,m2),
 (1<=m2 & 1<=m1 & 1<=v | m2<=(0-1) & m1<=(0-1) & 1<=v | m1<=(0-1) & 1<=m2 & 
  1<=v | m2<=(0-1) & 1<=m1 & 1<=v) --> RP(d,v,m1,m2),
 ((v<d' & 1<=m2 & 1<=d' & 1<=m1 | m1<=(0-1) & v<d' & m2<=(0-1) & 1<=d' | 
  v<d' & m2<=(0-1) & 1<=d' & 1<=m1 | m1<=(0-1) & v<d' & 1<=d' & 1<=m2) & 
  RP(d',v,m1_1823,m2_1824)) --> RP(d,v,m1,m2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure ripple$int~int~int~int~node~node SUCCESS

Termination checking result:

Stop Omega... 1180 invocations 
0 false contexts at: ()

Total verification time: 1.61 second(s)
	Time spent in main process: 0.36 second(s)
	Time spent in child processes: 1.25 second(s)
