#!/usr/bin/python
import math

N = 30

def f(x):
  y = x*x - 1.0
  return y
  

try:
  x = float(raw_input('Choose x = '))
  fixpoint = 2.0
  for i in range(N):
    # print distance 
    #distance = abs(x - fixpoint)
    #print distance
    
    # print value
    print x
    
    # update new value
    x = f(x)
except ValueError:
  print 'Not a number!'


