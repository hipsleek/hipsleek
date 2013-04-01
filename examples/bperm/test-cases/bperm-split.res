Starting z3... 

Entail (1) : Valid. 

 <1>EXISTS(bperm_9_110,bperm_9_109,bperm_9_108,Anon_135,bperm_3_134,bperm_3_133: x::cell( (c2_118,bperm_9_109,bperm_3_133))<Anon_135>[Orig]&bperm_3_134=0 & bperm_3_133=0 & 0<bperm_9_110 & bperm_9_110<=bperm_9_109 & bperm_9_110=2 & bperm_9_109=2 & bperm_9_108=0 & Anon_12=Anon_13 & c2_118<bperm_9_109 & 0<c2_118 & bperm_9_109=2 & bperm_9_110=c2_118+1 & 0<1 & 1<bperm_9_109&{FLOW,(19,20)=__norm})[]


Entail (2) : Valid. 

 <1>EXISTS(bperm_13_176,bperm_13_175,bperm_13_174,bperm_3_203,bperm_3_202: emp&bperm_3_203=0 & bperm_3_202=0 & 0<bperm_13_176 & bperm_13_176<=bperm_13_175 & bperm_13_176=2 & bperm_13_175=2 & bperm_13_174=0 & Anon_14=Anon_15&{FLOW,(19,20)=__norm})[]


Entail (3) : Fail.


Entail (4) : Valid. 

 <1>EXISTS(c2_375,bperm_21_364,bperm_21_363,bperm_21_362,bperm_3_391,bperm_3_390,Anon_417,bperm_3_416,bperm_3_415: x::cell( (c2_400,bperm_21_363,bperm_3_415))<Anon_417>[Orig]&bperm_3_416=0 & bperm_3_415=0 & 0<c2_375 & c2_375<=bperm_21_363 & bperm_3_391=0 & bperm_3_390=0 & 0<bperm_21_364 & bperm_21_364<=bperm_21_363 & bperm_21_364=3 & bperm_21_363=3 & bperm_21_362=0 & Anon_20=Anon_21 & c2_400<bperm_21_363 & 0<c2_400 & bperm_21_363=3 & bperm_21_363=3 & 1<bperm_21_363 & 0<1 & 1<bperm_21_363 & 0<(c2_400+1) & (c2_400+1)<bperm_21_363 & bperm_21_364=c2_400+1+1&{FLOW,(19,20)=__norm})[]


Entail (5) : Valid. 

 <1>EXISTS(c2_483,bperm_25_469,bperm_25_468,bperm_25_467,bperm_3_499,bperm_3_498,bperm_3_524,bperm_3_523: emp&bperm_3_524=0 & bperm_3_523=0 & 0<c2_483 & c2_483<=bperm_25_468 & bperm_3_499=0 & bperm_3_498=0 & 0<bperm_25_469 & bperm_25_469<=bperm_25_468 & bperm_25_469=3 & bperm_25_468=3 & bperm_25_467=0 & Anon_23=Anon_24&{FLOW,(19,20)=__norm})[]


Entail (6) : Fail.

Stop z3... 24 invocations 
SAT Count   : 6
SAT % Hit   : 66.66%
IMPLY Count : 52
IMPLY % Hit : 57.69%
Time(cache overhead) : 0. (seconds)

Total verification time: 0.15 second(s)
	Time spent in main process: 0.14 second(s)
	Time spent in child processes: 0.01 second(s)

