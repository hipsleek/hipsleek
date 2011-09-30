Assuming given method, synchronization on only one barrier:
 
 -> for each method, construct part of the barrier graph
 
 -> found examples in parsec 2.1 : 
      streamcluster.cpp
      fluidanimate/src/pthreads.cpp
      canneal/src/anneal_thread.cpp
      bodytrack/src/trackingbenchmark/threads/workergroup.cpp
      bodytrack/src/trackingbenchmark/trackingmodelomp.cpp
      bodytrack/src/trackingbenchmark/particlefilter.h
      bodytrack/src/trackingbenchmark/particlefilterpthread.h
 
 -> patterns found  (same code on all threads): 
     1) barrier ; call; barrier ; call ...
     2) loop { code ; barrier; }
          a) both the code and the barrier exited the loop 
          b) the code exited the loop, the barrier did not -> sequences of loops?
     3) few branches
