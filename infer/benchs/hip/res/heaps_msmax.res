
Processing file "heaps_msmax.ss"
Parsing heaps_msmax.ss ...
Parsing ../../../prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...

Checking procedure ripple$int~int~int~int~node~node... 
Procedure ripple$int~int~int~int~node~node SUCCESS

Checking procedure deletemax$node... 
!!! REL :  DELM(mx,mx2,res)
!!! POST:  mx2>=0 & res>=mx2 & mx>=res
!!! PRE :  0<=mx
!!! OLD SPECS: ((None,[]),EInfer [DELM]
              EBase exists (Expl)(Impl)[n; 
                    mx](ex)t::pq<n,mx>@M[Orig][LHSCase]@ rem br[{325}]&(
                    ([0!=n & 0<=n][0<=mx][null!=t]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 61::ref [t]
                                EXISTS(flted_205_53,
                                mx2: t'::pq<flted_205_53,mx2>@M[Orig][LHSCase]@ rem br[{326,325}]&
                                (
                                ([0<=flted_205_53 & 1+flted_205_53=n]
                                 [0<=mx2 & DELM(mx,mx2,res)]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; 
                  mx](ex)t::pq<n,mx>@M[Orig][LHSCase]@ rem br[{325}]&(
                  ([1<=n][0<=mx][t!=null]))&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop][0<=mx]))&{FLOW,(1,23)=__flow}
                            EAssume 61::ref [t]
                              EXISTS(flted_205_3334,
                              mx2_3335: t'::pq<flted_205_3334,mx2_3335>@M[Orig][LHSCase]@ rem br[{326,325}]&
                              (
                              ([res<=mx & 0<=mx & 0<=mx2_3335 & mx2_3335<=res]
                               [0<=flted_205_3334 & 0<=n & 1+flted_205_3334=n]
                               ))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(v_int_223_617':exists(d_1922:mx2=0 & exists(maxi_2096:res<=mx & 
  v_int_223_617'=res & d_1922=res & 0<=maxi_2096 & 
  maxi_2096<=res)))) --> DELM(mx,mx2,res),
 (exists(mx2_1928:exists(mx1:exists(mx3_2151:exists(max1_2418:exists(mx1_2081:exists(mx1_1925:exists(max2_2419:exists(v_54':res<=mx & 
  exists(maxi_2153:exists(tval_2422:maxi_2153<=res & 
  exists(mx3_2420:exists(mx4_2152:mx3_2420<=tval_2422 & 0<=mx3_2420 & 
  exists(mx4_2421:(mx2_1928=mx2 & mx1_1925=maxi_2153 & mx1=maxi_2153 & 
  mx4_2152=max2_2419 & mx3_2151=mx1_2081 & max1_2418=mx1_2081 & 
  v_54'<=mx1_2081 & mx3_2420<=mx1_2081 & mx1_2081<=max2_2419 & 
  max2_2419<=mx2 & mx2<=maxi_2153 & tval_2422<=max2_2419 & 0<=v_54' | 
  mx2_1928=mx2 & maxi_2153=mx2 & mx1=mx1_1925 & mx3_2151=mx1_2081 & 
  max1_2418=max2_2419 & v_54'=max2_2419 & tval_2422<=max2_2419 & (1+
  mx1_2081)<=max2_2419 & (1+mx4_2152)<=max2_2419 & max2_2419<=mx2 & 
  mx3_2420<=mx1_2081 & mx1_2081<=mx1_1925 & (1+mx1_1925)<=mx2 & 
  mx4_2421<=mx4_2152 | mx2_1928=mx2 & mx1_1925=maxi_2153 & mx1=maxi_2153 & 
  mx3_2151=mx1_2081 & max1_2418=max2_2419 & v_54'=max2_2419 & (1+
  mx1_2081)<=max2_2419 & (1+mx4_2152)<=max2_2419 & tval_2422<=max2_2419 & 
  max2_2419<=maxi_2153 & mx4_2421<=mx4_2152 & mx4_2152<=mx2 & 
  mx2<=maxi_2153 & tval_2422<=mx2 & mx3_2420<=mx1_2081 | mx2_1928=mx2 & 
  maxi_2153=mx2 & mx1=mx1_1925 & max2_2419=mx1_2081 & mx3_2151=mx1_2081 & 
  max1_2418=mx1_2081 & v_54'<=mx1_2081 & (1+mx4_2152)<=mx1_2081 & 
  tval_2422<=mx1_2081 & mx1_2081<=mx1_1925 & (1+mx1_1925)<=mx2 & 
  mx4_2421<=mx4_2152 & 0<=v_54' | mx2_1928=mx2 & mx1_1925=maxi_2153 & 
  mx1=maxi_2153 & max2_2419=mx1_2081 & mx3_2151=mx1_2081 & 
  max1_2418=mx1_2081 & v_54'<=mx1_2081 & (1+mx4_2152)<=mx1_2081 & 
  tval_2422<=mx1_2081 & mx1_2081<=maxi_2153 & mx4_2421<=mx4_2152 & 
  mx4_2152<=mx2 & mx2<=maxi_2153 & tval_2422<=mx2 & 0<=v_54' | 
  mx2_1928=mx2 & maxi_2153=mx2 & mx1=mx1_1925 & mx4_2152=max2_2419 & 
  mx3_2151=mx1_2081 & v_54'=max1_2418 & mx3_2420<=mx1_2081 & (1+
  mx1_2081)<=max1_2418 & max1_2418<=max2_2419 & max2_2419<=mx2 & 
  mx1_2081<=mx1_1925 & (1+mx1_1925)<=mx2 & tval_2422<=max2_2419 | 
  mx2_1928=mx2 & mx1_1925=maxi_2153 & mx1=maxi_2153 & mx4_2152=max2_2419 & 
  mx3_2151=mx1_2081 & v_54'=max1_2418 & mx3_2420<=mx1_2081 & (1+
  mx1_2081)<=max1_2418 & max1_2418<=max2_2419 & max2_2419<=mx2 & 
  mx2<=maxi_2153 & tval_2422<=max2_2419 | mx2_1928=mx2 & maxi_2153=mx2 & 
  mx1=mx1_1925 & mx4_2152=max2_2419 & mx3_2151=mx1_2081 & 
  max1_2418=mx1_2081 & v_54'<=mx1_2081 & mx3_2420<=mx1_2081 & 
  mx1_2081<=max2_2419 & max2_2419<=mx2 & mx1_2081<=mx1_1925 & (1+
  mx1_1925)<=mx2 & tval_2422<=max2_2419 & 0<=v_54') & mx4_2421<=tval_2422 & 
  0<=mx4_2421)))))))))))))) --> DELM(mx,mx2,res),
 (exists(v_int_223_617':exists(d_1922:mx2=0 & exists(mx1:res<=mx & 
  v_int_223_617'=res & d_1922=res & 0<=mx1 & 
  mx1<=res)))) --> DELM(mx,mx2,res),
 (exists(mx2_1928:exists(mx1:exists(mx3_2151:exists(max1_2515:exists(mx1_2081:exists(mx1_1925:exists(max2_2516:exists(v_54':res<=mx & 
  exists(maxi_2153:exists(tval_2519:maxi_2153<=res & 
  exists(mx3_2517:exists(mx4_2152:mx3_2517<=tval_2519 & 0<=mx3_2517 & 
  exists(mx4_2518:(mx2_1928=mx2 & mx1_1925=maxi_2153 & mx1=maxi_2153 & 
  mx4_2152=max2_2516 & mx3_2151=mx1_2081 & max1_2515=mx1_2081 & 
  v_54'<=mx1_2081 & mx3_2517<=mx1_2081 & mx1_2081<=max2_2516 & 
  max2_2516<=mx2 & mx2<=maxi_2153 & tval_2519<=max2_2516 & 0<=v_54' | 
  mx2_1928=mx2 & maxi_2153=mx2 & mx1=mx1_1925 & mx3_2151=mx1_2081 & 
  max1_2515=max2_2516 & v_54'=max2_2516 & tval_2519<=max2_2516 & (1+
  mx1_2081)<=max2_2516 & (1+mx4_2152)<=max2_2516 & max2_2516<=mx2 & 
  mx3_2517<=mx1_2081 & mx1_2081<=mx1_1925 & (1+mx1_1925)<=mx2 & 
  mx4_2518<=mx4_2152 | mx2_1928=mx2 & mx1_1925=maxi_2153 & mx1=maxi_2153 & 
  mx3_2151=mx1_2081 & max1_2515=max2_2516 & v_54'=max2_2516 & (1+
  mx1_2081)<=max2_2516 & (1+mx4_2152)<=max2_2516 & tval_2519<=max2_2516 & 
  max2_2516<=maxi_2153 & mx4_2518<=mx4_2152 & mx4_2152<=mx2 & 
  mx2<=maxi_2153 & tval_2519<=mx2 & mx3_2517<=mx1_2081 | mx2_1928=mx2 & 
  maxi_2153=mx2 & mx1=mx1_1925 & max2_2516=mx1_2081 & mx3_2151=mx1_2081 & 
  max1_2515=mx1_2081 & v_54'<=mx1_2081 & (1+mx4_2152)<=mx1_2081 & 
  tval_2519<=mx1_2081 & mx1_2081<=mx1_1925 & (1+mx1_1925)<=mx2 & 
  mx4_2518<=mx4_2152 & 0<=v_54' | mx2_1928=mx2 & mx1_1925=maxi_2153 & 
  mx1=maxi_2153 & max2_2516=mx1_2081 & mx3_2151=mx1_2081 & 
  max1_2515=mx1_2081 & v_54'<=mx1_2081 & (1+mx4_2152)<=mx1_2081 & 
  tval_2519<=mx1_2081 & mx1_2081<=maxi_2153 & mx4_2518<=mx4_2152 & 
  mx4_2152<=mx2 & mx2<=maxi_2153 & tval_2519<=mx2 & 0<=v_54' | 
  mx2_1928=mx2 & maxi_2153=mx2 & mx1=mx1_1925 & mx4_2152=max2_2516 & 
  mx3_2151=mx1_2081 & v_54'=max1_2515 & mx3_2517<=mx1_2081 & (1+
  mx1_2081)<=max1_2515 & max1_2515<=max2_2516 & max2_2516<=mx2 & 
  mx1_2081<=mx1_1925 & (1+mx1_1925)<=mx2 & tval_2519<=max2_2516 | 
  mx2_1928=mx2 & mx1_1925=maxi_2153 & mx1=maxi_2153 & mx4_2152=max2_2516 & 
  mx3_2151=mx1_2081 & v_54'=max1_2515 & mx3_2517<=mx1_2081 & (1+
  mx1_2081)<=max1_2515 & max1_2515<=max2_2516 & max2_2516<=mx2 & 
  mx2<=maxi_2153 & tval_2519<=max2_2516 | mx2_1928=mx2 & maxi_2153=mx2 & 
  mx1=mx1_1925 & mx4_2152=max2_2516 & mx3_2151=mx1_2081 & 
  max1_2515=mx1_2081 & v_54'<=mx1_2081 & mx3_2517<=mx1_2081 & 
  mx1_2081<=max2_2516 & max2_2516<=mx2 & mx1_2081<=mx1_1925 & (1+
  mx1_1925)<=mx2 & tval_2519<=max2_2516 & 0<=v_54') & mx4_2518<=tval_2519 & 
  0<=mx4_2518)))))))))))))) --> DELM(mx,mx2,res),
 (exists(v_int_223_617':exists(d_1922:mx2=0 & exists(mx1:res<=mx & 
  v_int_223_617'=res & d_1922=res & 0<=mx1 & 
  mx1<=res)))) --> DELM(mx,mx2,res),
 (exists(v_int_223_617':exists(d_1922:mx2=0 & exists(mx1:res<=mx & 
  v_int_223_617'=res & d_1922=res & 0<=mx1 & 
  mx1<=res)))) --> DELM(mx,mx2,res),
 (exists(mx2_1928:exists(mx1:exists(mx3_2151:exists(max1_2612:exists(mx1_2081:exists(mx1_1925:exists(max2_2613:exists(v_54':res<=mx & 
  exists(maxi_2153:exists(tval_2616:maxi_2153<=res & 
  exists(mx3_2614:exists(mx4_2152:mx3_2614<=tval_2616 & 0<=mx3_2614 & 
  exists(mx4_2615:(mx2_1928=mx2 & mx1_1925=maxi_2153 & mx1=maxi_2153 & 
  mx4_2152=max2_2613 & mx3_2151=mx1_2081 & max1_2612=mx1_2081 & 
  v_54'<=mx1_2081 & mx3_2614<=mx1_2081 & mx1_2081<=max2_2613 & 
  max2_2613<=mx2 & mx2<=maxi_2153 & tval_2616<=max2_2613 & 0<=v_54' | 
  mx2_1928=mx2 & maxi_2153=mx2 & mx1=mx1_1925 & mx3_2151=mx1_2081 & 
  max1_2612=max2_2613 & v_54'=max2_2613 & tval_2616<=max2_2613 & (1+
  mx1_2081)<=max2_2613 & (1+mx4_2152)<=max2_2613 & max2_2613<=mx2 & 
  mx3_2614<=mx1_2081 & mx1_2081<=mx1_1925 & (1+mx1_1925)<=mx2 & 
  mx4_2615<=mx4_2152 | mx2_1928=mx2 & mx1_1925=maxi_2153 & mx1=maxi_2153 & 
  mx3_2151=mx1_2081 & max1_2612=max2_2613 & v_54'=max2_2613 & (1+
  mx1_2081)<=max2_2613 & (1+mx4_2152)<=max2_2613 & tval_2616<=max2_2613 & 
  max2_2613<=maxi_2153 & mx4_2615<=mx4_2152 & mx4_2152<=mx2 & 
  mx2<=maxi_2153 & tval_2616<=mx2 & mx3_2614<=mx1_2081 | mx2_1928=mx2 & 
  maxi_2153=mx2 & mx1=mx1_1925 & max2_2613=mx1_2081 & mx3_2151=mx1_2081 & 
  max1_2612=mx1_2081 & v_54'<=mx1_2081 & (1+mx4_2152)<=mx1_2081 & 
  tval_2616<=mx1_2081 & mx1_2081<=mx1_1925 & (1+mx1_1925)<=mx2 & 
  mx4_2615<=mx4_2152 & 0<=v_54' | mx2_1928=mx2 & mx1_1925=maxi_2153 & 
  mx1=maxi_2153 & max2_2613=mx1_2081 & mx3_2151=mx1_2081 & 
  max1_2612=mx1_2081 & v_54'<=mx1_2081 & (1+mx4_2152)<=mx1_2081 & 
  tval_2616<=mx1_2081 & mx1_2081<=maxi_2153 & mx4_2615<=mx4_2152 & 
  mx4_2152<=mx2 & mx2<=maxi_2153 & tval_2616<=mx2 & 0<=v_54' | 
  mx2_1928=mx2 & maxi_2153=mx2 & mx1=mx1_1925 & mx4_2152=max2_2613 & 
  mx3_2151=mx1_2081 & v_54'=max1_2612 & mx3_2614<=mx1_2081 & (1+
  mx1_2081)<=max1_2612 & max1_2612<=max2_2613 & max2_2613<=mx2 & 
  mx1_2081<=mx1_1925 & (1+mx1_1925)<=mx2 & tval_2616<=max2_2613 | 
  mx2_1928=mx2 & mx1_1925=maxi_2153 & mx1=maxi_2153 & mx4_2152=max2_2613 & 
  mx3_2151=mx1_2081 & v_54'=max1_2612 & mx3_2614<=mx1_2081 & (1+
  mx1_2081)<=max1_2612 & max1_2612<=max2_2613 & max2_2613<=mx2 & 
  mx2<=maxi_2153 & tval_2616<=max2_2613 | mx2_1928=mx2 & maxi_2153=mx2 & 
  mx1=mx1_1925 & mx4_2152=max2_2613 & mx3_2151=mx1_2081 & 
  max1_2612=mx1_2081 & v_54'<=mx1_2081 & mx3_2614<=mx1_2081 & 
  mx1_2081<=max2_2613 & max2_2613<=mx2 & mx1_2081<=mx1_1925 & (1+
  mx1_1925)<=mx2 & tval_2616<=max2_2613 & 0<=v_54') & mx4_2615<=tval_2616 & 
  0<=mx4_2615)))))))))))))) --> DELM(mx,mx2,res),
 (exists(v_int_223_617':exists(d_1922:mx2=0 & exists(mx1:res<=mx & 
  v_int_223_617'=res & d_1922=res & 0<=mx1 & 
  mx1<=res)))) --> DELM(mx,mx2,res),
 (exists(v_int_223_617':exists(d_1922:mx2=0 & exists(mx1:res<=mx & 
  v_int_223_617'=res & d_1922=res & 0<=mx1 & 
  mx1<=res)))) --> DELM(mx,mx2,res),
 (exists(v_int_223_617':exists(d_1922:mx2=0 & exists(mx1:res<=mx & 
  v_int_223_617'=res & d_1922=res & 0<=mx1 & 
  mx1<=res)))) --> DELM(mx,mx2,res),
 (exists(mx2_1928:exists(mx1:exists(mx3_2151:exists(max1_2765:exists(mx1_2081:exists(mx1_1925:exists(max2_2766:exists(v_54':res<=mx & 
  exists(maxi_2153:exists(tval_2769:maxi_2153<=res & 
  exists(mx3_2767:exists(mx4_2152:mx3_2767<=tval_2769 & 0<=mx3_2767 & 
  exists(mx4_2768:(mx2_1928=mx2 & mx1_1925=maxi_2153 & mx1=maxi_2153 & 
  mx4_2152=max2_2766 & mx3_2151=mx1_2081 & max1_2765=mx1_2081 & 
  v_54'<=mx1_2081 & mx3_2767<=mx1_2081 & mx1_2081<=max2_2766 & 
  max2_2766<=mx2 & mx2<=maxi_2153 & tval_2769<=max2_2766 & 0<=v_54' | 
  mx2_1928=mx2 & maxi_2153=mx2 & mx1=mx1_1925 & mx3_2151=mx1_2081 & 
  max1_2765=max2_2766 & v_54'=max2_2766 & tval_2769<=max2_2766 & (1+
  mx1_2081)<=max2_2766 & (1+mx4_2152)<=max2_2766 & max2_2766<=mx2 & 
  mx3_2767<=mx1_2081 & mx1_2081<=mx1_1925 & (1+mx1_1925)<=mx2 & 
  mx4_2768<=mx4_2152 | mx2_1928=mx2 & mx1_1925=maxi_2153 & mx1=maxi_2153 & 
  mx3_2151=mx1_2081 & max1_2765=max2_2766 & v_54'=max2_2766 & (1+
  mx1_2081)<=max2_2766 & (1+mx4_2152)<=max2_2766 & tval_2769<=max2_2766 & 
  max2_2766<=maxi_2153 & mx4_2768<=mx4_2152 & mx4_2152<=mx2 & 
  mx2<=maxi_2153 & tval_2769<=mx2 & mx3_2767<=mx1_2081 | mx2_1928=mx2 & 
  maxi_2153=mx2 & mx1=mx1_1925 & max2_2766=mx1_2081 & mx3_2151=mx1_2081 & 
  max1_2765=mx1_2081 & v_54'<=mx1_2081 & (1+mx4_2152)<=mx1_2081 & 
  tval_2769<=mx1_2081 & mx1_2081<=mx1_1925 & (1+mx1_1925)<=mx2 & 
  mx4_2768<=mx4_2152 & 0<=v_54' | mx2_1928=mx2 & mx1_1925=maxi_2153 & 
  mx1=maxi_2153 & max2_2766=mx1_2081 & mx3_2151=mx1_2081 & 
  max1_2765=mx1_2081 & v_54'<=mx1_2081 & (1+mx4_2152)<=mx1_2081 & 
  tval_2769<=mx1_2081 & mx1_2081<=maxi_2153 & mx4_2768<=mx4_2152 & 
  mx4_2152<=mx2 & mx2<=maxi_2153 & tval_2769<=mx2 & 0<=v_54' | 
  mx2_1928=mx2 & maxi_2153=mx2 & mx1=mx1_1925 & mx4_2152=max2_2766 & 
  mx3_2151=mx1_2081 & v_54'=max1_2765 & mx3_2767<=mx1_2081 & (1+
  mx1_2081)<=max1_2765 & max1_2765<=max2_2766 & max2_2766<=mx2 & 
  mx1_2081<=mx1_1925 & (1+mx1_1925)<=mx2 & tval_2769<=max2_2766 | 
  mx2_1928=mx2 & mx1_1925=maxi_2153 & mx1=maxi_2153 & mx4_2152=max2_2766 & 
  mx3_2151=mx1_2081 & v_54'=max1_2765 & mx3_2767<=mx1_2081 & (1+
  mx1_2081)<=max1_2765 & max1_2765<=max2_2766 & max2_2766<=mx2 & 
  mx2<=maxi_2153 & tval_2769<=max2_2766 | mx2_1928=mx2 & maxi_2153=mx2 & 
  mx1=mx1_1925 & mx4_2152=max2_2766 & mx3_2151=mx1_2081 & 
  max1_2765=mx1_2081 & v_54'<=mx1_2081 & mx3_2767<=mx1_2081 & 
  mx1_2081<=max2_2766 & max2_2766<=mx2 & mx1_2081<=mx1_1925 & (1+
  mx1_1925)<=mx2 & tval_2769<=max2_2766 & 0<=v_54') & mx4_2768<=tval_2769 & 
  0<=mx4_2768)))))))))))))) --> DELM(mx,mx2,res),
 (exists(v_int_223_617':exists(d_1922:mx2=0 & exists(maxi_2176:res<=mx & 
  v_int_223_617'=res & d_1922=res & 0<=maxi_2176 & 
  maxi_2176<=res)))) --> DELM(mx,mx2,res),
 (exists(mx2_1928:exists(mx1:exists(mx3_2231:exists(max1_2844:exists(mx1_2081:exists(mx1_1925:exists(max2_2845:exists(v_54':res<=mx & 
  exists(maxi_2233:exists(tval_2848:maxi_2233<=res & 
  exists(mx3_2846:exists(mx4_2232:mx3_2846<=tval_2848 & 0<=mx3_2846 & 
  exists(mx4_2847:(mx2_1928=mx2 & mx1_1925=maxi_2233 & mx1=maxi_2233 & 
  mx4_2232=max2_2845 & mx3_2231=mx1_2081 & max1_2844=mx1_2081 & 
  v_54'<=mx1_2081 & mx3_2846<=mx1_2081 & mx1_2081<=max2_2845 & 
  max2_2845<=mx2 & mx2<=maxi_2233 & tval_2848<=max2_2845 & 0<=v_54' | 
  mx2_1928=mx2 & maxi_2233=mx2 & mx1=mx1_1925 & mx3_2231=mx1_2081 & 
  max1_2844=max2_2845 & v_54'=max2_2845 & tval_2848<=max2_2845 & (1+
  mx1_2081)<=max2_2845 & (1+mx4_2232)<=max2_2845 & max2_2845<=mx2 & 
  mx3_2846<=mx1_2081 & mx1_2081<=mx1_1925 & (1+mx1_1925)<=mx2 & 
  mx4_2847<=mx4_2232 | mx2_1928=mx2 & mx1_1925=maxi_2233 & mx1=maxi_2233 & 
  mx3_2231=mx1_2081 & max1_2844=max2_2845 & v_54'=max2_2845 & (1+
  mx1_2081)<=max2_2845 & (1+mx4_2232)<=max2_2845 & tval_2848<=max2_2845 & 
  max2_2845<=maxi_2233 & mx4_2847<=mx4_2232 & mx4_2232<=mx2 & 
  mx2<=maxi_2233 & tval_2848<=mx2 & mx3_2846<=mx1_2081 | mx2_1928=mx2 & 
  maxi_2233=mx2 & mx1=mx1_1925 & max2_2845=mx1_2081 & mx3_2231=mx1_2081 & 
  max1_2844=mx1_2081 & v_54'<=mx1_2081 & (1+mx4_2232)<=mx1_2081 & 
  tval_2848<=mx1_2081 & mx1_2081<=mx1_1925 & (1+mx1_1925)<=mx2 & 
  mx4_2847<=mx4_2232 & 0<=v_54' | mx2_1928=mx2 & mx1_1925=maxi_2233 & 
  mx1=maxi_2233 & max2_2845=mx1_2081 & mx3_2231=mx1_2081 & 
  max1_2844=mx1_2081 & v_54'<=mx1_2081 & (1+mx4_2232)<=mx1_2081 & 
  tval_2848<=mx1_2081 & mx1_2081<=maxi_2233 & mx4_2847<=mx4_2232 & 
  mx4_2232<=mx2 & mx2<=maxi_2233 & tval_2848<=mx2 & 0<=v_54' | 
  mx2_1928=mx2 & maxi_2233=mx2 & mx1=mx1_1925 & mx4_2232=max2_2845 & 
  mx3_2231=mx1_2081 & v_54'=max1_2844 & mx3_2846<=mx1_2081 & (1+
  mx1_2081)<=max1_2844 & max1_2844<=max2_2845 & max2_2845<=mx2 & 
  mx1_2081<=mx1_1925 & (1+mx1_1925)<=mx2 & tval_2848<=max2_2845 | 
  mx2_1928=mx2 & mx1_1925=maxi_2233 & mx1=maxi_2233 & mx4_2232=max2_2845 & 
  mx3_2231=mx1_2081 & v_54'=max1_2844 & mx3_2846<=mx1_2081 & (1+
  mx1_2081)<=max1_2844 & max1_2844<=max2_2845 & max2_2845<=mx2 & 
  mx2<=maxi_2233 & tval_2848<=max2_2845 | mx2_1928=mx2 & maxi_2233=mx2 & 
  mx1=mx1_1925 & mx4_2232=max2_2845 & mx3_2231=mx1_2081 & 
  max1_2844=mx1_2081 & v_54'<=mx1_2081 & mx3_2846<=mx1_2081 & 
  mx1_2081<=max2_2845 & max2_2845<=mx2 & mx1_2081<=mx1_1925 & (1+
  mx1_1925)<=mx2 & tval_2848<=max2_2845 & 0<=v_54') & mx4_2847<=tval_2848 & 
  0<=mx4_2847)))))))))))))) --> DELM(mx,mx2,res),
 (exists(v_int_223_617':exists(d_1922:mx2=0 & exists(mx1_1925:res<=mx & 
  v_int_223_617'=res & d_1922=res & 0<=mx1_1925 & 
  mx1_1925<=res)))) --> DELM(mx,mx2,res),
 (exists(mx2_1928:exists(mx1:exists(mx3_2231:exists(max1_2943:exists(mx1_2081:exists(mx1_1925:exists(max2_2944:exists(v_54':res<=mx & 
  exists(maxi_2233:exists(tval_2947:maxi_2233<=res & 
  exists(mx3_2945:exists(mx4_2232:mx3_2945<=tval_2947 & 0<=mx3_2945 & 
  exists(mx4_2946:(mx2_1928=mx2 & mx1_1925=maxi_2233 & mx1=maxi_2233 & 
  mx4_2232=max2_2944 & mx3_2231=mx1_2081 & max1_2943=mx1_2081 & 
  v_54'<=mx1_2081 & mx3_2945<=mx1_2081 & mx1_2081<=max2_2944 & 
  max2_2944<=mx2 & mx2<=maxi_2233 & tval_2947<=max2_2944 & 0<=v_54' | 
  mx2_1928=mx2 & maxi_2233=mx2 & mx1=mx1_1925 & mx3_2231=mx1_2081 & 
  max1_2943=max2_2944 & v_54'=max2_2944 & tval_2947<=max2_2944 & (1+
  mx1_2081)<=max2_2944 & (1+mx4_2232)<=max2_2944 & max2_2944<=mx2 & 
  mx3_2945<=mx1_2081 & mx1_2081<=mx1_1925 & (1+mx1_1925)<=mx2 & 
  mx4_2946<=mx4_2232 | mx2_1928=mx2 & mx1_1925=maxi_2233 & mx1=maxi_2233 & 
  mx3_2231=mx1_2081 & max1_2943=max2_2944 & v_54'=max2_2944 & (1+
  mx1_2081)<=max2_2944 & (1+mx4_2232)<=max2_2944 & tval_2947<=max2_2944 & 
  max2_2944<=maxi_2233 & mx4_2946<=mx4_2232 & mx4_2232<=mx2 & 
  mx2<=maxi_2233 & tval_2947<=mx2 & mx3_2945<=mx1_2081 | mx2_1928=mx2 & 
  maxi_2233=mx2 & mx1=mx1_1925 & max2_2944=mx1_2081 & mx3_2231=mx1_2081 & 
  max1_2943=mx1_2081 & v_54'<=mx1_2081 & (1+mx4_2232)<=mx1_2081 & 
  tval_2947<=mx1_2081 & mx1_2081<=mx1_1925 & (1+mx1_1925)<=mx2 & 
  mx4_2946<=mx4_2232 & 0<=v_54' | mx2_1928=mx2 & mx1_1925=maxi_2233 & 
  mx1=maxi_2233 & max2_2944=mx1_2081 & mx3_2231=mx1_2081 & 
  max1_2943=mx1_2081 & v_54'<=mx1_2081 & (1+mx4_2232)<=mx1_2081 & 
  tval_2947<=mx1_2081 & mx1_2081<=maxi_2233 & mx4_2946<=mx4_2232 & 
  mx4_2232<=mx2 & mx2<=maxi_2233 & tval_2947<=mx2 & 0<=v_54' | 
  mx2_1928=mx2 & maxi_2233=mx2 & mx1=mx1_1925 & mx4_2232=max2_2944 & 
  mx3_2231=mx1_2081 & v_54'=max1_2943 & mx3_2945<=mx1_2081 & (1+
  mx1_2081)<=max1_2943 & max1_2943<=max2_2944 & max2_2944<=mx2 & 
  mx1_2081<=mx1_1925 & (1+mx1_1925)<=mx2 & tval_2947<=max2_2944 | 
  mx2_1928=mx2 & mx1_1925=maxi_2233 & mx1=maxi_2233 & mx4_2232=max2_2944 & 
  mx3_2231=mx1_2081 & v_54'=max1_2943 & mx3_2945<=mx1_2081 & (1+
  mx1_2081)<=max1_2943 & max1_2943<=max2_2944 & max2_2944<=mx2 & 
  mx2<=maxi_2233 & tval_2947<=max2_2944 | mx2_1928=mx2 & maxi_2233=mx2 & 
  mx1=mx1_1925 & mx4_2232=max2_2944 & mx3_2231=mx1_2081 & 
  max1_2943=mx1_2081 & v_54'<=mx1_2081 & mx3_2945<=mx1_2081 & 
  mx1_2081<=max2_2944 & max2_2944<=mx2 & mx1_2081<=mx1_1925 & (1+
  mx1_1925)<=mx2 & tval_2947<=max2_2944 & 0<=v_54') & mx4_2946<=tval_2947 & 
  0<=mx4_2946)))))))))))))) --> DELM(mx,mx2,res),
 (exists(v_int_223_617':exists(d_1922:mx2=0 & exists(mx1_1925:res<=mx & 
  v_int_223_617'=res & d_1922=res & 0<=mx1_1925 & 
  mx1_1925<=res)))) --> DELM(mx,mx2,res),
 (exists(v_int_223_617':exists(d_1922:mx2=0 & exists(mx1_1925:res<=mx & 
  v_int_223_617'=res & d_1922=res & 0<=mx1_1925 & 
  mx1_1925<=res)))) --> DELM(mx,mx2,res),
 (exists(mx2_1928:exists(mx1:exists(mx3_2231:exists(max1_3042:exists(mx1_2081:exists(mx1_1925:exists(max2_3043:exists(v_54':res<=mx & 
  exists(maxi_2233:exists(tval_3046:maxi_2233<=res & 
  exists(mx3_3044:exists(mx4_2232:mx3_3044<=tval_3046 & 0<=mx3_3044 & 
  exists(mx4_3045:(mx2_1928=mx2 & mx1_1925=maxi_2233 & mx1=maxi_2233 & 
  mx4_2232=max2_3043 & mx3_2231=mx1_2081 & max1_3042=mx1_2081 & 
  v_54'<=mx1_2081 & mx3_3044<=mx1_2081 & mx1_2081<=max2_3043 & 
  max2_3043<=mx2 & mx2<=maxi_2233 & tval_3046<=max2_3043 & 0<=v_54' | 
  mx2_1928=mx2 & maxi_2233=mx2 & mx1=mx1_1925 & mx3_2231=mx1_2081 & 
  max1_3042=max2_3043 & v_54'=max2_3043 & tval_3046<=max2_3043 & (1+
  mx1_2081)<=max2_3043 & (1+mx4_2232)<=max2_3043 & max2_3043<=mx2 & 
  mx3_3044<=mx1_2081 & mx1_2081<=mx1_1925 & (1+mx1_1925)<=mx2 & 
  mx4_3045<=mx4_2232 | mx2_1928=mx2 & mx1_1925=maxi_2233 & mx1=maxi_2233 & 
  mx3_2231=mx1_2081 & max1_3042=max2_3043 & v_54'=max2_3043 & (1+
  mx1_2081)<=max2_3043 & (1+mx4_2232)<=max2_3043 & tval_3046<=max2_3043 & 
  max2_3043<=maxi_2233 & mx4_3045<=mx4_2232 & mx4_2232<=mx2 & 
  mx2<=maxi_2233 & tval_3046<=mx2 & mx3_3044<=mx1_2081 | mx2_1928=mx2 & 
  maxi_2233=mx2 & mx1=mx1_1925 & max2_3043=mx1_2081 & mx3_2231=mx1_2081 & 
  max1_3042=mx1_2081 & v_54'<=mx1_2081 & (1+mx4_2232)<=mx1_2081 & 
  tval_3046<=mx1_2081 & mx1_2081<=mx1_1925 & (1+mx1_1925)<=mx2 & 
  mx4_3045<=mx4_2232 & 0<=v_54' | mx2_1928=mx2 & mx1_1925=maxi_2233 & 
  mx1=maxi_2233 & max2_3043=mx1_2081 & mx3_2231=mx1_2081 & 
  max1_3042=mx1_2081 & v_54'<=mx1_2081 & (1+mx4_2232)<=mx1_2081 & 
  tval_3046<=mx1_2081 & mx1_2081<=maxi_2233 & mx4_3045<=mx4_2232 & 
  mx4_2232<=mx2 & mx2<=maxi_2233 & tval_3046<=mx2 & 0<=v_54' | 
  mx2_1928=mx2 & maxi_2233=mx2 & mx1=mx1_1925 & mx4_2232=max2_3043 & 
  mx3_2231=mx1_2081 & v_54'=max1_3042 & mx3_3044<=mx1_2081 & (1+
  mx1_2081)<=max1_3042 & max1_3042<=max2_3043 & max2_3043<=mx2 & 
  mx1_2081<=mx1_1925 & (1+mx1_1925)<=mx2 & tval_3046<=max2_3043 | 
  mx2_1928=mx2 & mx1_1925=maxi_2233 & mx1=maxi_2233 & mx4_2232=max2_3043 & 
  mx3_2231=mx1_2081 & v_54'=max1_3042 & mx3_3044<=mx1_2081 & (1+
  mx1_2081)<=max1_3042 & max1_3042<=max2_3043 & max2_3043<=mx2 & 
  mx2<=maxi_2233 & tval_3046<=max2_3043 | mx2_1928=mx2 & maxi_2233=mx2 & 
  mx1=mx1_1925 & mx4_2232=max2_3043 & mx3_2231=mx1_2081 & 
  max1_3042=mx1_2081 & v_54'<=mx1_2081 & mx3_3044<=mx1_2081 & 
  mx1_2081<=max2_3043 & max2_3043<=mx2 & mx1_2081<=mx1_1925 & (1+
  mx1_1925)<=mx2 & tval_3046<=max2_3043 & 0<=v_54') & mx4_3045<=tval_3046 & 
  0<=mx4_3045)))))))))))))) --> DELM(mx,mx2,res),
 (exists(v_int_223_617':exists(d_1922:mx2=0 & exists(maxi_2176:res<=mx & 
  v_int_223_617'=res & d_1922=res & 0<=maxi_2176 & 
  maxi_2176<=res)))) --> DELM(mx,mx2,res),
 (exists(v_int_223_617':exists(d_1922:mx2=0 & exists(mx1:res<=mx & 
  v_int_223_617'=res & d_1922=res & 0<=mx1 & 
  mx1<=res)))) --> DELM(mx,mx2,res),
 (exists(v_int_223_617':exists(d_1922:mx2=0 & exists(maxi_2176:res<=mx & 
  v_int_223_617'=res & d_1922=res & 0<=maxi_2176 & 
  maxi_2176<=res)))) --> DELM(mx,mx2,res),
 (exists(v_int_223_617':exists(d_1922:mx2=0 & exists(mx1_1925:res<=mx & 
  v_int_223_617'=res & d_1922=res & 0<=mx1_1925 & 
  mx1_1925<=res)))) --> DELM(mx,mx2,res),
 (exists(v_int_223_617':exists(d_1922:mx2=0 & exists(mx1:res<=mx & 
  v_int_223_617'=res & d_1922=res & 0<=mx1 & 
  mx1<=res)))) --> DELM(mx,mx2,res),
 (mx2=0 & 0<=res & res<=mx) --> DELM(mx,mx2,res),
 (exists(v_int_223_617':exists(d_1922:mx2=0 & exists(mx1:res<=mx & 
  v_int_223_617'=res & d_1922=res & 0<=mx1 & 
  mx1<=res)))) --> DELM(mx,mx2,res),
 (exists(mx2_1928:exists(mx1:exists(mx3_2231:exists(max1_3297:exists(mx1_2081:exists(mx1_1925:exists(max2_3298:exists(v_54':res<=mx & 
  exists(maxi_2233:exists(tval_3301:maxi_2233<=res & 
  exists(mx3_3299:exists(mx4_2232:mx3_3299<=tval_3301 & 0<=mx3_3299 & 
  exists(mx4_3300:(mx2_1928=mx2 & mx1_1925=maxi_2233 & mx1=maxi_2233 & 
  mx4_2232=max2_3298 & mx3_2231=mx1_2081 & max1_3297=mx1_2081 & 
  v_54'<=mx1_2081 & mx3_3299<=mx1_2081 & mx1_2081<=max2_3298 & 
  max2_3298<=mx2 & mx2<=maxi_2233 & tval_3301<=max2_3298 & 0<=v_54' | 
  mx2_1928=mx2 & maxi_2233=mx2 & mx1=mx1_1925 & mx3_2231=mx1_2081 & 
  max1_3297=max2_3298 & v_54'=max2_3298 & tval_3301<=max2_3298 & (1+
  mx1_2081)<=max2_3298 & (1+mx4_2232)<=max2_3298 & max2_3298<=mx2 & 
  mx3_3299<=mx1_2081 & mx1_2081<=mx1_1925 & (1+mx1_1925)<=mx2 & 
  mx4_3300<=mx4_2232 | mx2_1928=mx2 & mx1_1925=maxi_2233 & mx1=maxi_2233 & 
  mx3_2231=mx1_2081 & max1_3297=max2_3298 & v_54'=max2_3298 & (1+
  mx1_2081)<=max2_3298 & (1+mx4_2232)<=max2_3298 & tval_3301<=max2_3298 & 
  max2_3298<=maxi_2233 & mx4_3300<=mx4_2232 & mx4_2232<=mx2 & 
  mx2<=maxi_2233 & tval_3301<=mx2 & mx3_3299<=mx1_2081 | mx2_1928=mx2 & 
  maxi_2233=mx2 & mx1=mx1_1925 & max2_3298=mx1_2081 & mx3_2231=mx1_2081 & 
  max1_3297=mx1_2081 & v_54'<=mx1_2081 & (1+mx4_2232)<=mx1_2081 & 
  tval_3301<=mx1_2081 & mx1_2081<=mx1_1925 & (1+mx1_1925)<=mx2 & 
  mx4_3300<=mx4_2232 & 0<=v_54' | mx2_1928=mx2 & mx1_1925=maxi_2233 & 
  mx1=maxi_2233 & max2_3298=mx1_2081 & mx3_2231=mx1_2081 & 
  max1_3297=mx1_2081 & v_54'<=mx1_2081 & (1+mx4_2232)<=mx1_2081 & 
  tval_3301<=mx1_2081 & mx1_2081<=maxi_2233 & mx4_3300<=mx4_2232 & 
  mx4_2232<=mx2 & mx2<=maxi_2233 & tval_3301<=mx2 & 0<=v_54' | 
  mx2_1928=mx2 & maxi_2233=mx2 & mx1=mx1_1925 & mx4_2232=max2_3298 & 
  mx3_2231=mx1_2081 & v_54'=max1_3297 & mx3_3299<=mx1_2081 & (1+
  mx1_2081)<=max1_3297 & max1_3297<=max2_3298 & max2_3298<=mx2 & 
  mx1_2081<=mx1_1925 & (1+mx1_1925)<=mx2 & tval_3301<=max2_3298 | 
  mx2_1928=mx2 & mx1_1925=maxi_2233 & mx1=maxi_2233 & mx4_2232=max2_3298 & 
  mx3_2231=mx1_2081 & v_54'=max1_3297 & mx3_3299<=mx1_2081 & (1+
  mx1_2081)<=max1_3297 & max1_3297<=max2_3298 & max2_3298<=mx2 & 
  mx2<=maxi_2233 & tval_3301<=max2_3298 | mx2_1928=mx2 & maxi_2233=mx2 & 
  mx1=mx1_1925 & mx4_2232=max2_3298 & mx3_2231=mx1_2081 & 
  max1_3297=mx1_2081 & v_54'<=mx1_2081 & mx3_3299<=mx1_2081 & 
  mx1_2081<=max2_3298 & max2_3298<=mx2 & mx1_2081<=mx1_1925 & (1+
  mx1_1925)<=mx2 & tval_3301<=max2_3298 & 0<=v_54') & mx4_3300<=tval_3301 & 
  0<=mx4_3300)))))))))))))) --> DELM(mx,mx2,res)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure deletemax$node SUCCESS

Checking procedure deleteone$int~int~node~node... 
!!! OLD SPECS: ((None,[]),EInfer [mx1,mx2,mx3,mx4]
              EBase exists (Expl)(Impl)[mx1; mx2](ex)EXISTS(m1_65,
                    m2_66: l::pq<m1_65,mx1>@M[Orig][LHSCase]@ rem br[{325}] * 
                    r::pq<m2_66,mx2>@M[Orig][LHSCase]@ rem br[{326,325}]&(
                    ([m1=m1_65 & m2=m2_66 & 0!=m1_65 & 0<=m1_65 & (-1+
                       m1)<=m2 & m2<=m1]
                     [0<=mx1][null!=l][0<=mx2]))&
                    {FLOW,(20,21)=__norm})
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 39::ref [m1;m2;l;r]
                                EXISTS(m1_67,m2_68,
                                maxi: l'::pq<m1_67,mx3>@M[Orig][LHSCase]@ rem br[{326,325}] * 
                                r'::pq<m2_68,mx4>@M[Orig][LHSCase]@ rem br[{326,325}]&
                                (
                                ([maxi=max(mx1,mx2) & res<=maxi & 0<=res]
                                 [m1'=m1_67 & m2'=m2_68 & 0<=m2_68 & (-1+
                                   m1')<=m2' & m2'<=m1' & m1'+m2'=-1+m1+m2]
                                 [0<=mx3][0<=mx4]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[mx1; 
                  mx2](ex)l::pq<m1_65,mx1>@M[Orig][LHSCase]@ rem br[{325}] * 
                  r::pq<m2_66,mx2>@M[Orig][LHSCase]@ rem br[{326,325}]&(
                  ([0<=mx1][l!=null][0<=mx2]
                   [m2=m2_66 & m1=m1_65 & m2<=m1 & (-1+m1)<=m2 & 1<=m1]))&
                  {FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 39::ref [m1;m2;l;r]
                              
                              EXISTS(maxi_3400: l'::pq<m1_67,mx3>@M[Orig][LHSCase]@ rem br[{326,325}] * 
                              r'::pq<m2_68,mx4>@M[Orig][LHSCase]@ rem br[{326,325}]&
                              (
                              ([l!=null]
                               [m2_68=m1_67 & m2_68=m1' & m2_68=m2' & 
                                 m2_68=m2 & -1+m1=m2_68 & 0<=m2_68]
                               [mx1=maxi_3400 & mx3=mx4 & mx3=mx2 & 0<=mx1 & 
                                 res<=maxi_3400 & 0<=mx2 & mx3<=maxi_3400 & 
                                 0<=res]
                               [r=r'][0<=m2_66][0<=m1_65]))&
                              {FLOW,(20,21)=__norm})
                              or EXISTS(maxi_3401: l'::pq<m1_67,mx3>@M[Orig][LHSCase]@ rem br[{326,325}] * 
                                 r'::pq<m2_68,mx4>@M[Orig][LHSCase]@ rem br[{326,325}]&
                                 (
                                 ([(m2=m1 & m2'=m1-1 & m2_68=m1-1 & m1'=m1 & 
                                    maxi_3401=mx3 & mx1=mx3 & mx4=mx2 & 
                                    l'=l & m1_67=m1 & 0<=res & res<=mx2 & 
                                    mx2<=mx3 & r!=null & l!=null & 1<=m1 | 
                                    m2=m1 & m2'=m1-1 & m2_68=m1-1 & m1'=m1 & 
                                    maxi_3401=mx2 & mx1=mx3 & mx4=mx2 & 
                                    l'=l & m1_67=m1 & 0<=mx3 & mx3<mx2 & 
                                    0<=res & res<=mx2 & r!=null & l!=null & 
                                    1<=m1) & 0<=mx2 & 0<=mx1]
                                  [0<=m2_66][0<=m1_65]))&
                                 {FLOW,(20,21)=__norm})
                              )
!!! NEW RELS:[]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure deleteone$int~int~node~node SUCCESS

Checking procedure deleteoneel$node... 
Procedure deleteoneel$node SUCCESS

Checking procedure insert$node~int... 
Procedure insert$node~int SUCCESS

Termination checking result:

Stop Omega... 3271 invocations 
1 false contexts at: ( (155,2) )

Total verification time: 89.5 second(s)
	Time spent in main process: 81.9 second(s)
	Time spent in child processes: 7.6 second(s)
