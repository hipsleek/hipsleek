
Processing file "heaps.ss"
Parsing heaps.ss ...
Parsing /home2/loris/hg/sl_infer/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure deleteoneel$node... 
Procedure deleteoneel$node SUCCESS
Checking procedure deleteone$int~int~node~node... 
Procedure deleteone$int~int~node~node SUCCESS
Checking procedure ripple$int~int~int~int~node~node... 
dprint: heaps.ss:282: ctx:  List of Failesc Context: [FEC(0, 1, 1  [(139::,1 ); (139::,1 ); (138::,1 ); (138::,1 ); (137::,1 ); (137::,1 ); 
(136::,1 ); (136::,1 )])]

Successful States:
[
 Label: [(139::,1 ); (139::,1 ); (138::,1 ); (138::,1 ); (137::,1 ); (137::,1
          ); (136::,1 ); (136::,1 )]
 State:l'::node<d_1673,m1_1675,m2_1678,l_1674,r_1677>@M[Orig][] * l_1674::pq<m1_1670,mx1_1676>@M[Orig]@ rem br[{322,321}] * r_1677::pq<m2_1671,mx2_1679>@M[Orig]@ rem br[{322,321}] * r'::node<d_1730,m1_1732,m2_1735,l_1731,r_1734>@M[Orig][] * l_1731::pq<m1_1727,mx1_1733>@M[Orig]@ rem br[{322,321}] * r_1734::pq<m2_1728,mx2_1736>@M[Orig]@ rem br[{322,321}] & (([
                                                                    v'=v & 
                                                                    d=d' & 
                                                                    0<=mx2_1679 & 
                                                                    0<=mx2_1736 & 
                                                                    0<=v & 
                                                                    0<=mx2 & 
                                                                    (1+
                                                                    d_1673)<=d_1730 & 
                                                                    d_1673<=mx1 & 
                                                                    (1+
                                                                    v')<=d_1730 & 
                                                                    mx1_1676<=d_1673 & 
                                                                    mx2_1679<=d_1673 & 
                                                                    d_1730<=mx2 & 
                                                                    mx1_1733<=d_1730 & 
                                                                    mx1<=d & 
                                                                    0<=mx1_1676 & 
                                                                    v<=d & 
                                                                    mx2_1736<=d_1730 & 
                                                                    0<=mx1 & 
                                                                    mx2<=d & 
                                                                    0<=mx1_1733]
                                                                    [m2_1728=m2_1735 & 
                                                                    m1_1727=m1_1732 & 
                                                                    m2_1671=m2_1678 & 
                                                                    m1_1670=m1_1675 & 
                                                                    m1=m1' & 
                                                                    m2=m2' & 
                                                                    0<=m2_1728 & 
                                                                    m2_1678+
                                                                    m3_1672=m1_1675 & 
                                                                    0<=m2' & 
                                                                    m2'=1+
                                                                    m1_1732+
                                                                    m2_1735 & 
                                                                    m3_1672<=1 & 
                                                                    0!=m2' & 
                                                                    m2_1735+
                                                                    m3_1729=m1_1732 & 
                                                                    m2<=m1 & 
                                                                    0!=m1' & 
                                                                    m3_1729<=1 & 
                                                                    0<=m2_1671 & 
                                                                    (-1+
                                                                    m1)<=m2 & 
                                                                    0<=m3_1672 & 
                                                                    0<=m3_1729 & 
                                                                    m1'=1+
                                                                    m1_1675+
                                                                    m2_1678]
                                                                    [r=r' & 
                                                                    null!=r]
                                                                    [!(v_bool_244_765')]
                                                                    [!(v_bool_253_764')]
                                                                    [l=l' & 
                                                                    null!=l]
                                                                    [!(v_bool_266_763')]
                                                                    [!(v_bool_278_762')]
                                                                    )) & {FLOW,(20,21)=__norm}
 ]

Procedure ripple$int~int~int~int~node~node SUCCESS
Checking procedure deletemax$node... 
dprint: heaps.ss:365: ctx:  List of Failesc Context: [FEC(0, 1, 1  [(120::,1 ); (120::,1 )]) FEC(0, 1, 1  [(120::,1 ); (120::,1 )])]

Successful States:
[
 Label: [(120::,1 ); (120::,1 )]
 State:or[EXISTS(maxi_2500: tleft_58'::pq<tnleft_56',mx2>@M[Orig][LHSCase]@ rem br[{321}] * tright_59'::pq<tnleft_56',mx2>@M[Orig][LHSCase]@ rem br[{321}] & (([
                                                                    0<=m1_64]
                                                                    [0<=m2_65]
                                                                    [m1_2357=m1_2362 & 
                                                                    null=r_2364 & 
                                                                    m2_2358=m2_2365 & 
                                                                    m2_2358=0 & 
                                                                    m2_2358=tnright_57' & 
                                                                    m2_2358=tnleft_56' & 
                                                                    (0=m2_2358 | 
                                                                    null=r_2364) & 
                                                                    m2_2365+
                                                                    m3_2359=m1_2362 & 
                                                                    0<=n & 
                                                                    (-1+
                                                                    tnleft_56')<=tnright_57' & 
                                                                    0!=n & 
                                                                    m3_2359<=1 & 
                                                                    tnright_57'<=tnleft_56' & 
                                                                    n=1+
                                                                    m1_2362+
                                                                    m2_2365 & 
                                                                    0!=m1_2357 & 
                                                                    0<=m3_2359 & 
                                                                    tnleft_56'+
                                                                    tnright_57'=-1+
                                                                    m1_2357+
                                                                    tnleft_56']
                                                                    [!(v_bool_355_609')]
                                                                    [v_boolean_355_2425]
                                                                    [t=t' & 
                                                                    null!=t]
                                                                    [null!=l_2361]
                                                                    [787::!(v_boolean_355_2424)]
                                                                    [tval_55'=d_2360 & 
                                                                    mx1_2363=mx1 & 
                                                                    mx2_2366=0 & 
                                                                    mx2_2366=mx2 & 
                                                                    maxi_2500=max(mx1,
                                                                    mx2) & 
                                                                    0<=mx1_2363 & 
                                                                    d_2360<=mx & 
                                                                    mx1_2363<=d_2360 & 
                                                                    mx2<=mx1 & 
                                                                    v_53'<=maxi_2500 & 
                                                                    0<=v_53' & 
                                                                    0<=mx2 & 
                                                                    mx2_2366<=d_2360 & 
                                                                    0<=mx]
                                                                    [tleft_58'=null]
                                                                    [tright_59'=null]
                                                                    )) & {FLOW,(20,21)=__norm}); 
         EXISTS(mx3_2496,mx4_2497,maxi_2498: tleft_58'::pq<tnleft_56',mx3_2496>@M[Orig][LHSCase]@ rem br[{322}] * tright_59'::pq<tnright_57',mx4_2497>@M[Orig][LHSCase]@ rem br[{322,321}] & (([
                                                                    0<=m1_64]
                                                                    [0<=m2_65]
                                                                    [787::!(v_boolean_355_2428)]
                                                                    [null!=l_2361]
                                                                    [mx2=mx2_2366 & 
                                                                    tval_55'=d_2360 & 
                                                                    mx1_2363=mx1 & 
                                                                    maxi_2498=max(mx1,
                                                                    mx2) & 
                                                                    0<=mx3_2496 & 
                                                                    0<=mx1_2363 & 
                                                                    mx3_2496<=mx1 & 
                                                                    0<=mx2_2366 & 
                                                                    mx4_2497<=mx2 & 
                                                                    d_2360<=mx & 
                                                                    0<=v_53' & 
                                                                    mx1_2363<=d_2360 & 
                                                                    mx2_2366<=d_2360 & 
                                                                    0<=mx4_2497 & 
                                                                    v_53'<=maxi_2498 & 
                                                                    0<=mx]
                                                                    [t=t' & 
                                                                    null!=t]
                                                                    [m2_2358=m2_2365 & 
                                                                    m1_2357=m1_2362 & 
                                                                    m2_2365+
                                                                    m3_2359=m1_2362 & 
                                                                    0<=m2_2358 & 
                                                                    0!=tnleft_56' & 
                                                                    (-1+
                                                                    tnleft_56')<=tnright_57' & 
                                                                    tnright_57'<=tnleft_56' & 
                                                                    0!=m2_2358 & 
                                                                    n=1+
                                                                    m1_2362+
                                                                    m2_2365 & 
                                                                    0<=n & 
                                                                    m3_2359<=1 & 
                                                                    0!=m1_2357 & 
                                                                    0<=tnright_57' & 
                                                                    0!=n & 
                                                                    tnleft_56'+
                                                                    tnright_57'=-1+
                                                                    m1_2362+
                                                                    m2_2365 & 
                                                                    0<=m3_2359]
                                                                    [null!=r_2364]
                                                                    [767::!(v_boolean_355_2429)]
                                                                    [!(v_bool_355_609')]
                                                                    [null!=tleft_58']
                                                                    )) & {FLOW,(20,21)=__norm})]
 ],

Successful States:
[
 Label: [(120::,1 ); (120::,1 )]
 State:or[EXISTS(maxi_2506: r_2364::pq<m2_2358,mx2_2366>@M[Orig]@ rem br[{321}] * tleft_58'::pq<tnleft_56',mx2>@M[Orig][LHSCase]@ rem br[{321}] * tright_59'::pq<tnleft_56',mx2>@M[Orig][LHSCase]@ rem br[{321}] & (([
                                                                    0<=m1_64]
                                                                    [0<=m2_65]
                                                                    [!(v_bool_355_609')]
                                                                    [v_boolean_355_2425]
                                                                    [null=r_2364]
                                                                    [m1_2357=m1_2362 & 
                                                                    m2_2358=m2_2365 & 
                                                                    m2_2358=0 & 
                                                                    m2_2358=tnright_57' & 
                                                                    m2_2358=tnleft_56' & 
                                                                    m2_2365+
                                                                    m3_2359=m1_2362 & 
                                                                    0<=m3_2359 & 
                                                                    (-1+
                                                                    tnleft_56')<=tnright_57' & 
                                                                    tnright_57'<=tnleft_56' & 
                                                                    0!=n & 
                                                                    n=1+
                                                                    m1_2362+
                                                                    m2_2365 & 
                                                                    0<=n & 
                                                                    m3_2359<=1 & 
                                                                    0!=m1_2357 & 
                                                                    tnleft_56'+
                                                                    tnright_57'=-1+
                                                                    m1_2357+
                                                                    tnleft_56']
                                                                    [t=t' & 
                                                                    null!=t]
                                                                    [null!=l_2361]
                                                                    [787::!(v_boolean_355_2424)]
                                                                    [tval_55'=d_2360 & 
                                                                    mx1_2363=mx1 & 
                                                                    mx2_2366=0 & 
                                                                    mx2_2366=mx2 & 
                                                                    maxi_2506=max(mx1,
                                                                    mx2) & 
                                                                    v_53'<=maxi_2506 & 
                                                                    0<=v_53' & 
                                                                    mx1_2363<=d_2360 & 
                                                                    mx2_2366<=d_2360 & 
                                                                    d_2360<=mx & 
                                                                    0<=mx1_2363 & 
                                                                    0<=mx2 & 
                                                                    mx2<=mx1 & 
                                                                    0<=mx]
                                                                    [tleft_58'=null]
                                                                    [tright_59'=null]
                                                                    )) & {FLOW,(20,21)=__norm}); 
         EXISTS(mx3_2502,mx4_2503,maxi_2504: tleft_58'::pq<tnleft_56',mx3_2502>@M[Orig][LHSCase]@ rem br[{322}] * tright_59'::pq<tnright_57',mx4_2503>@M[Orig][LHSCase]@ rem br[{322,321}] & (([
                                                                    0<=m1_64]
                                                                    [0<=m2_65]
                                                                    [787::!(v_boolean_355_2428)]
                                                                    [null!=l_2361]
                                                                    [mx2=mx2_2366 & 
                                                                    tval_55'=d_2360 & 
                                                                    mx1_2363=mx1 & 
                                                                    maxi_2504=max(mx1,
                                                                    mx2) & 
                                                                    0<=mx3_2502 & 
                                                                    0<=mx1_2363 & 
                                                                    mx3_2502<=mx1 & 
                                                                    0<=mx2_2366 & 
                                                                    mx4_2503<=mx2 & 
                                                                    d_2360<=mx & 
                                                                    0<=v_53' & 
                                                                    mx1_2363<=d_2360 & 
                                                                    mx2_2366<=d_2360 & 
                                                                    0<=mx4_2503 & 
                                                                    v_53'<=maxi_2504 & 
                                                                    0<=mx]
                                                                    [t=t' & 
                                                                    null!=t]
                                                                    [m2_2358=m2_2365 & 
                                                                    m1_2357=m1_2362 & 
                                                                    m2_2365+
                                                                    m3_2359=m1_2362 & 
                                                                    0<=m2_2358 & 
                                                                    0!=tnleft_56' & 
                                                                    (-1+
                                                                    tnleft_56')<=tnright_57' & 
                                                                    tnright_57'<=tnleft_56' & 
                                                                    0!=m2_2358 & 
                                                                    n=1+
                                                                    m1_2362+
                                                                    m2_2365 & 
                                                                    0<=n & 
                                                                    m3_2359<=1 & 
                                                                    0!=m1_2357 & 
                                                                    0<=tnright_57' & 
                                                                    0!=n & 
                                                                    tnleft_56'+
                                                                    tnright_57'=-1+
                                                                    m1_2362+
                                                                    m2_2365 & 
                                                                    0<=m3_2359]
                                                                    [null!=r_2364]
                                                                    [767::!(v_boolean_355_2429)]
                                                                    [!(v_bool_355_609')]
                                                                    [null!=tleft_58']
                                                                    )) & {FLOW,(20,21)=__norm})]
 ]

Procedure deletemax$node SUCCESS
Checking procedure insert$node~int... 
Procedure insert$node~int SUCCESS
Stop Omega... 3296 invocations 
1 false contexts at: ( (246,2) )

Total verification time: 11.832738 second(s)
	Time spent in main process: 7.436464 second(s)
	Time spent in child processes: 4.396274 second(s)
