/usr/local/bin/mona

Processing file "heaps_msmaxb.ss"
Parsing heaps_msmaxb.ss ...
Parsing /home/thaitm/hg-repository/final/sleekex/prelude.ss ...
Starting Reduce... 
Translating global variables to procedure parameters...
Starting Omega...oc

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Checking procedure deleteone$int~int~node~node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure deleteone$int~int~node~node SUCCESS

Checking procedure insert$node~int... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

!!! REL :  INS(S1,S2)
!!! POST:  S1<subset> S2 
!!! PRE :  true
!!! OLD SPECS: ((None,[]),EInfer [INS]
              EBase exists (Expl)(Impl)[n; mx; 
                    S1](ex)t::pq1<n,mx,S1>@M[Orig][LHSCase]@ rem br[{281,280}]&
                    (([true][true][true]))&{FLOW,(20,21)=__norm}
                      EBase true&MayLoop&{FLOW,(1,23)=__flow}
                              EAssume 1::
                                EXISTS(flted_29_59,ma,
                                S2: res::pq1<flted_29_59,ma,S2>@M[Orig][LHSCase]@ rem br[{280}]&
                                (
                                ([-1+flted_29_59=n]
                                 [(mx<=v & ma=v | ma=mx) & {v}<subset> S2  & 
                                   S2!=() & INS(S1,S2)]
                                 [null!=res]))&
                                {FLOW,(20,21)=__norm}))
!!! NEW SPECS: ((None,[]),EBase exists (Expl)(Impl)[n; mx; 
                  S1](ex)t::pq1<n,mx,S1>@M[Orig][LHSCase]@ rem br[{281,280}]&
                  (())&{FLOW,(20,21)=__norm}
                    EBase true&(([MayLoop]))&{FLOW,(1,23)=__flow}
                            EAssume 1::
                              EXISTS(flted_29_2680,ma_2681,
                              S2_2682: res::pq1<flted_29_2680,ma_2681,S2_2682>@M[Orig][LHSCase]@ rem br[{280}]&
                              (
                              ([null!=res]
                               [(mx<=v & ma_2681=v | ma_2681=mx) & 
                                 {v}<subset> S2_2682  & S1<subset> S2_2682
                                  & S2_2682!=() & 0<=mx]
                               [-1+flted_29_2680=n & 0<=n]))&
                              {FLOW,(20,21)=__norm}))
!!! NEW RELS:[ (exists(v:exists(ma:exists(S1_2270:exists(S2_2274:exists(d_2266:v=ma & 
  S1_2270= & S2_2274= & 0<=ma & d_2266=ma & S1= & S2=union(S1_2270,S2_2274,
  {d_2266}))))))) --> INS(S1,S2),
 (exists(mx_1799:exists(mx1_1605:exists(d_1602:exists(S2_1610:exists(S2_2301:exists(S1_2297:exists(S1_1606:exists(d_2293:exists(mx:exists(mx2_1609:exists(mx2_2300:exists(v:exists(ma:exists(mx1_2296:exists(ma_1852:(mx=d_1602 & 
  mx_1799=mx1_1605 & ma_1852=d_1602 & mx1_1605<=d_1602 & mx2_2300<=d_1602 & 
  (1+d_1602)<=ma & 0<=mx1_1605 | mx=d_1602 & mx_1799=mx1_1605 & 
  ma_1852=mx1_1605 & mx2_2300<=d_1602 & mx1_1605<=d_1602 & (1+d_1602)<=ma & 
  0<=mx1_1605) & S1!=() & S1=union(S1_1606,S2_1610,{d_1602}) & 
  S2=union(S1_2297,S2_2301,{d_2293}) & INS(S1_1800,S2_1853) & 
  S2_1610=S2_2301 & S2_1853=S1_2297 & S1_1606=S1_1800 & d_2293=ma & 
  {mx}<subset> S2_1853  & S2_1853!=() & mx2_1609=mx2_2300 & v=ma & 
  mx1_2296=ma_1852)))))))))))))))) --> INS(S1,S2),
 (exists(mx2_1609:exists(mx_1936:exists(d_1602:exists(S2_2383:exists(S1_2379:exists(S2_1610:exists(d_2375:exists(v:exists(ma:exists(mx:exists(S1_1606:exists(mx1_1605:exists(mx1_2378:exists(mx2_2382:exists(ma_1971:(d_1602=mx & 
  mx2_1609=mx_1936 & ma_1971=mx & mx_1936<=mx & mx1_2378<=mx & (1+mx)<=ma & 
  0<=mx_1936 | d_1602=mx & mx2_1609=mx_1936 & ma_1971=mx_1936 & 
  mx1_2378<=mx & mx_1936<=mx & (1+mx)<=ma & 0<=mx_1936) & S1!=() & 
  S1=union(S1_1606,S2_1610,{d_1602}) & S2=union(S1_2379,S2_2383,{d_2375}) & 
  INS(S1_1937,S2_1972) & S2_1972=S2_2383 & S1_1606=S1_2379 & 
  S2_1610=S1_1937 & d_2375=ma & v=ma & {mx}<subset> S2_1972  & S2_1972!=() & 
  S1_1606!=() & mx1_1605=mx1_2378 & 
  mx2_2382=ma_1971)))))))))))))))) --> INS(S1,S2),
 (exists(mx1_1605:exists(mx_2088:exists(S2_1610:exists(S2_2475:exists(S1_2471:exists(S1_1606:exists(d_2467:exists(d_1602:exists(v:exists(mx2_1609:exists(mx2_2474:exists(mx1_2470:exists(ma_2131:exists(mx:exists(ma:(mx1_1605=mx_2088 & 
  ma_2131=v & 0<=mx_2088 & mx_2088<=v | mx1_1605=mx_2088 & ma_2131=mx_2088 & 
  v<=ma & 0<=mx_2088) & S1!=() & S1=union(S1_1606,S2_1610,{d_1602}) & 
  S2=union(S1_2471,S2_2475,{d_2467}) & INS(S1_2089,S2_2132) & 
  S2_1610=S2_2475 & S2_2132=S1_2471 & S1_1606=S1_2089 & d_2467=ma & 
  d_1602=ma & ma_2131<=ma & mx2_2474<=ma & {v}<subset> S2_2132  & 
  S2_2132!=() & mx2_1609=mx2_2474 & mx1_2470=ma_2131 & 
  mx=ma)))))))))))))))) --> INS(S1,S2),
 (exists(mx_2181:exists(mx2_1609:exists(S2_2548:exists(S1_2544:exists(S2_1610:exists(d_2540:exists(d_1602:exists(v:exists(S1_1606:exists(mx1_1605:exists(mx1_2543:exists(mx2_2547:exists(ma_2214:exists(mx:exists(ma:(mx_2181=mx2_1609 & 
  ma_2214=v & 0<=mx2_1609 & mx2_1609<=v | mx_2181=mx2_1609 & 
  ma_2214=mx2_1609 & v<=ma & 0<=mx2_1609) & S1=union(S1_1606,S2_1610,
  {d_1602}) & S1!=() & S2=union(S1_2544,S2_2548,{d_2540}) & 
  INS(S1_2182,S2_2215) & S2_2215=S2_2548 & S1_1606=S1_2544 & 
  S2_1610=S1_2182 & d_2540=ma & d_1602=ma & ma_2214<=ma & mx1_2543<=ma & 
  {v}<subset> S2_2215  & S2_2215!=() & S1_1606!=() & mx1_1605=mx1_2543 & 
  mx2_2547=ma_2214 & mx=ma)))))))))))))))) --> INS(S1,S2)]
!!! NEW ASSUME:[]
!!! NEW RANK:[]
Procedure insert$node~int SUCCESS

Checking procedure ripple$int~int~int~int~node~node... 
[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

[mona.ml]: Mona is preparing to restart because of upper limit reached
Restarting Mona ...

Procedure ripple$int~int~int~int~node~node SUCCESS

Termination checking result:


1 false contexts at: ( (156,2) )

Total verification time: 22.95 second(s)
	Time spent in main process: 1.67 second(s)
	Time spent in child processes: 21.28 second(s)
