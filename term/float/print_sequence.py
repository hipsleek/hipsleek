#!/usr/bin/python
import math

N = 200

def f(x):
  y = x * x  - 2.0
  return y
  
x = -0.6;
fixpoint = -1

for i in range(N):
  # print distance 
  #distance = abs(x - fixpoint)
  #print distance
  
  # print value
  print x
  
  # update new value
  x = f(x)

