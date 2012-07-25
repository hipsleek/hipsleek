#!/usr/bin/python
import math

N = 40

def f(x):
  y = 2 - 1/x
  return y
  
x = 0.2;
fixpoint = 1.0

for i in range(N):
  # print distance 
  distance = abs(x - fixpoint)
  print distance
  
  # print value
  # print x
  
  # update new value
  x = f(x)

