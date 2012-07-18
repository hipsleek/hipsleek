#!/usr/bin/python
import math

N = 20

def f(x):
  y = 1 + 2/x
  return y
  
x = 1.9;
fixpoint = 2.0

for i in range(N):
  # print distance 
  #distance = abs(x - fixpoint)
  #print distance
  
  # print value
  print x
  
  # update new value
  x = f(x)

