#!/usr/bin/python
import math

N = 30

def f(x):
  y = 1.0 + 2.0/x
  return y
  

try:
  x = float(raw_input('Choose x = '))
  fixpoint = 2.0
  for i in range(N):
    # print distance 
    dx = abs(x - fixpoint)
    #print distance
    
    # print value
    s =  "x = %8.5f          dx = %8.5f" % (x, dx)
    print s
    
    # update new value
    x = f(x)
except ValueError:
  print 'Not a number!'


