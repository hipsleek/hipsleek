
Processing file "avl-orig3.ss"
Parsing avl-orig3.ss ...
Parsing /home2/loris/hg/sl_infer/prelude.ss ...
Starting Reduce... 
Starting Omega...oc
Translating global variables to procedure parameters...
Checking procedure get_max$int~int... 
Procedure get_max$int~int SUCCESS
Checking procedure rotate_left_child$node... 
Procedure rotate_left_child$node SUCCESS
Checking procedure rotate_right_child$node... 
Procedure rotate_right_child$node SUCCESS
Checking procedure double_left_child$node... 
Procedure double_left_child$node SUCCESS
Checking procedure double_right_child$node... 
Procedure double_right_child$node SUCCESS
Checking procedure height$node... 
dprint: avl-orig3.ss:27: ctx:  List of Failesc Context: [FEC(0, 1, 1  )]

Successful States:
[
 Label: 
 State:x::avl<m,n,b>@M[Orig][LHSCase]@ rem br[{273,272}] & (([b<=2 & 0<=b]
                                                             [0<=n][0<=m]
                                                             [x=x'])) & {FLOW,(20,21)=__norm}
 ]

Procedure height$node SUCCESS
Checking procedure insert$node~int... 
Procedure insert$node~int SUCCESS
Stop Omega... 3205 invocations 
0 false contexts at: ()

Total verification time: 12.868802 second(s)
	Time spent in main process: 7.600474 second(s)
	Time spent in child processes: 5.268328 second(s)
